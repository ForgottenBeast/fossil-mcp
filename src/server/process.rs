//! Bounded `fossil` subprocess runner.
//!
//! Every child gets: piped stdin (closed after the payload), concurrent capped
//! stdout/stderr drains, one wall-clock deadline covering write + wait, and
//! its own process group that is killed as a whole when the call ends (normal
//! exit, timeout, output overflow, cancellation), so descendants cannot
//! outlive it. The leader is observed through a pidfd and reaped only after
//! the group was signalled, so a recycled pid is never signalled. Callers
//! never see raw child bytes in an error; they get a [`ProcError`] kind.

use std::ffi::OsString;
use std::os::fd::{FromRawFd, OwnedFd};
use std::path::Path;
use std::process::Stdio;
use std::time::Duration;
use tokio::io::unix::AsyncFd;
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWriteExt, Interest};
use tokio::process::Command;

/// Bounds applied to every `fossil` child.
#[derive(Debug, Clone, Copy)]
pub struct Limits {
    /// Wall-clock deadline for write + wait.
    pub deadline: Duration,
    /// Maximum stdout bytes retained before the child is killed.
    pub stdout_max: usize,
    /// Maximum stderr bytes retained before the child is killed.
    pub stderr_max: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            deadline: Duration::from_secs(10),
            stdout_max: 2 << 20,
            stderr_max: 64 << 10,
        }
    }
}

/// Captured result of a finished child.
#[derive(Debug)]
pub struct ProcOutput {
    /// Exit code; `None` when terminated by a signal.
    pub code: Option<i32>,
    /// Captured stdout (at most `stdout_max` bytes).
    pub stdout: Vec<u8>,
    /// Captured stderr (at most `stderr_max` bytes). Never forward to callers.
    pub stderr: Vec<u8>,
}

impl ProcOutput {
    /// True when the child exited with status 0.
    pub fn success(&self) -> bool {
        self.code == Some(0)
    }
}

/// Why a child run did not produce a [`ProcOutput`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProcError {
    /// The executable could not be started: it provably never ran.
    Spawn,
    /// The deadline elapsed; the child was killed. Its effect is unknown.
    Timeout,
    /// stdout or stderr exceeded its cap; the child was killed.
    OutputLimit,
    /// I/O failure after start (e.g. broken stdin pipe). Effect unknown.
    Io,
}

async fn drain<R: AsyncRead + Unpin>(mut r: R, max: usize) -> Result<Vec<u8>, ProcError> {
    let mut buf = Vec::new();
    let mut chunk = [0u8; 8192];
    loop {
        let n = r.read(&mut chunk).await.map_err(|_| ProcError::Io)?;
        if n == 0 {
            return Ok(buf);
        }
        if buf.len() + n > max {
            return Err(ProcError::OutputLimit);
        }
        buf.extend_from_slice(&chunk[..n]);
    }
}

/// Test instrumentation: every group signal and whether its leader was still
/// unreaped at that moment. Off unless [`kill_log::enable`] is called.
#[doc(hidden)]
pub mod kill_log {
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicBool, Ordering};

    /// One group-signal decision.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct GroupKill {
        /// The process group (= the leader's pid).
        pub pgid: i32,
        /// The leader had not been reaped when the signal was decided.
        pub leader_unreaped: bool,
    }

    static ON: AtomicBool = AtomicBool::new(false);
    static LOG: Mutex<Vec<GroupKill>> = Mutex::new(Vec::new());

    /// Start recording (process-wide).
    pub fn enable() {
        ON.store(true, Ordering::SeqCst);
    }

    pub(super) fn record(k: GroupKill) {
        if ON.load(Ordering::SeqCst) {
            LOG.lock().unwrap_or_else(|e| e.into_inner()).push(k);
        }
    }

    /// Recorded decisions for one process group.
    pub fn of(pgid: i32) -> Vec<GroupKill> {
        LOG.lock()
            .unwrap_or_else(|e| e.into_inner())
            .iter()
            .filter(|k| k.pgid == pgid)
            .copied()
            .collect()
    }
}

/// SIGKILL the group `pgid`, but only while its leader is still unreaped.
///
/// The group id is the leader's pid. While the leader is a running process or
/// an unreaped zombie that number cannot be handed to anyone else, so the
/// signal can only reach our own group. After the leader is reaped it could
/// be reused, so nothing is sent. `waitid(WNOWAIT)` observes without reaping.
fn kill_group(pgid: i32) {
    // SAFETY: waitid writes into a zeroed siginfo we own; killpg takes ints.
    let unreaped = unsafe {
        let mut info: libc::siginfo_t = std::mem::zeroed();
        libc::waitid(
            libc::P_PID,
            pgid as libc::id_t,
            &mut info,
            libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
        ) == 0
    };
    kill_log::record(kill_log::GroupKill {
        pgid,
        leader_unreaped: unreaped,
    });
    if unreaped {
        // SAFETY: plain syscall; an emptied group just yields ESRCH.
        unsafe {
            libc::killpg(pgid, libc::SIGKILL);
        }
    }
}

/// Kills the child's whole process group when dropped while still armed.
///
/// Armed from spawn until [`run`] has signalled the group itself, during
/// which time nothing reaps the leader (only `child.wait()` does, and it runs
/// strictly afterwards), so cancellation always hits an unreaped leader.
struct GroupGuard(Option<i32>);

impl GroupGuard {
    fn kill(&mut self) {
        if let Some(pgid) = self.0.take() {
            kill_group(pgid);
        }
    }
}

impl Drop for GroupGuard {
    fn drop(&mut self) {
        self.kill();
    }
}

/// Opens a pidfd for `pid`; it becomes readable when the process exits, and
/// waiting on it does not reap the process.
fn pidfd(pid: i32) -> std::io::Result<AsyncFd<OwnedFd>> {
    // SAFETY: pidfd_open takes integers; on success the fd is ours alone.
    let fd = unsafe { libc::syscall(libc::SYS_pidfd_open, pid, 0) };
    if fd < 0 {
        return Err(std::io::Error::last_os_error());
    }
    // SAFETY: `fd` is a fresh, valid descriptor returned above.
    let owned = unsafe { OwnedFd::from_raw_fd(fd as i32) };
    AsyncFd::with_interest(owned, Interest::READABLE)
}

/// Run `bin args…` with `stdin` bytes under `limits`.
///
/// The leader is observed (pidfd) but not reaped until the whole group has
/// been signalled, so a numeric group id is never signalled after reuse.
pub async fn run(
    bin: &Path,
    args: &[OsString],
    stdin: Option<&[u8]>,
    limits: &Limits,
) -> Result<ProcOutput, ProcError> {
    let mut child = Command::new(bin)
        .args(args)
        .stdin(if stdin.is_some() {
            Stdio::piped()
        } else {
            Stdio::null()
        })
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .kill_on_drop(true)
        .process_group(0)
        .spawn()
        .map_err(|_| ProcError::Spawn)?;
    // Declared after `child`, so it drops first: the group is signalled
    // while the leader is still unreaped, then the child is reaped.
    let mut guard = GroupGuard(child.id().and_then(|p| i32::try_from(p).ok()));
    let exited = match guard.0.map(pidfd) {
        Some(Ok(fd)) => fd,
        _ => {
            guard.kill();
            let _ = child.wait().await;
            return Err(ProcError::Io);
        }
    };

    let mut child_stdin = child.stdin.take();
    let out = child.stdout.take().expect("stdout piped");
    let err = child.stderr.take().expect("stderr piped");

    let io = async {
        let write = async {
            if let (Some(mut w), Some(bytes)) = (child_stdin.take(), stdin) {
                w.write_all(bytes).await.map_err(|_| ProcError::Io)?;
                w.shutdown().await.map_err(|_| ProcError::Io)?;
                drop(w);
            }
            Ok::<(), ProcError>(())
        };
        let (_, so, se, _) = tokio::try_join!(
            write,
            drain(out, limits.stdout_max),
            drain(err, limits.stderr_max),
            async {
                exited
                    .readable()
                    .await
                    .map(|_| ())
                    .map_err(|_| ProcError::Io)
            },
        )?;
        Ok::<_, ProcError>((so, se))
    };

    let res = match tokio::time::timeout(limits.deadline, io).await {
        Ok(r) => r,
        Err(_) => Err(ProcError::Timeout),
    };
    // Every path ends the same way: the leader is still unreaped here, so
    // signal the whole group (descendants included), then reap the leader.
    guard.kill();
    let status = match tokio::time::timeout(Duration::from_secs(5), child.wait()).await {
        Ok(Ok(s)) => s,
        _ => {
            let _ = child.start_kill();
            return Err(res.err().unwrap_or(ProcError::Io));
        }
    };
    let (stdout, stderr) = res?;
    Ok(ProcOutput {
        code: status.code(),
        stdout,
        stderr,
    })
}

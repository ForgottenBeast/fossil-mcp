//! Bounded `fossil` subprocess runner.
//!
//! Every child gets: piped stdin (closed after the payload), concurrent capped
//! stdout/stderr drains, one wall-clock deadline covering write + wait, and
//! `kill_on_drop` so cancellation reaps it. Callers never see raw child bytes
//! in an error; they get a [`ProcError`] kind.

use std::ffi::OsString;
use std::path::Path;
use std::process::Stdio;
use std::time::Duration;
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWriteExt};
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

/// Run `bin args…` with `stdin` bytes under `limits`.
pub async fn run(
    bin: &Path,
    args: &[OsString],
    stdin: Option<&[u8]>,
    limits: &Limits,
) -> Result<ProcOutput, ProcError> {
    let mut child = Command::new(bin)
        .args(args)
        .stdin(if stdin.is_some() { Stdio::piped() } else { Stdio::null() })
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .kill_on_drop(true)
        .spawn()
        .map_err(|_| ProcError::Spawn)?;

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
        let (_, so, se, status) = tokio::try_join!(
            write,
            drain(out, limits.stdout_max),
            drain(err, limits.stderr_max),
            async { child.wait().await.map_err(|_| ProcError::Io) },
        )?;
        Ok::<ProcOutput, ProcError>(ProcOutput {
            code: status.code(),
            stdout: so,
            stderr: se,
        })
    };

    let res = match tokio::time::timeout(limits.deadline, io).await {
        Ok(r) => r,
        Err(_) => Err(ProcError::Timeout),
    };
    if res.is_err() {
        let _ = child.kill().await; // kill + reap on every known error path
    }
    res
}

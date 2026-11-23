//! Process-group lifecycle: the group is signalled only while its leader is
//! still unreaped (so the numeric id cannot have been reused), and every
//! descendant is cleaned up on normal exit, deadline and cancellation.
use fossil_mcp::server::process::{self, Limits, ProcError, kill_log};
use std::path::Path;
use std::time::{Duration, Instant};

fn alive(pid: i32) -> bool {
    std::fs::read_to_string(format!("/proc/{pid}/stat"))
        .map(|s| !s.contains(") Z "))
        .unwrap_or(false)
}

async fn wait_dead(pid: i32, what: &str) {
    for _ in 0..100 {
        if !alive(pid) {
            return;
        }
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    panic!("{what} {pid} still alive");
}

fn pidfile(dir: &Path, name: &str) -> i32 {
    std::fs::read_to_string(dir.join(name))
        .unwrap()
        .trim()
        .parse()
        .unwrap()
}

fn limits(ms: u64) -> Limits {
    Limits {
        deadline: Duration::from_millis(ms),
        ..Default::default()
    }
}

async fn sh(script: String, ms: u64) -> Result<process::ProcOutput, ProcError> {
    process::run(
        Path::new("/bin/sh"),
        &["-c".into(), script.into()],
        None,
        &limits(ms),
    )
    .await
}

/// Leader exits at once; a descendant keeps stdout open until the deadline.
#[tokio::test]
async fn timeout_signals_the_group_while_the_leader_is_unreaped() {
    kill_log::enable();
    let d = tempfile::tempdir().unwrap();
    let p = d.path().display();
    let r = sh(
        format!("echo $$ > '{p}/leader'; sleep 30 & echo $! > '{p}/child'; exit 0"),
        1000,
    )
    .await;
    assert_eq!(r.unwrap_err(), ProcError::Timeout);
    let (leader, child) = (pidfile(d.path(), "leader"), pidfile(d.path(), "child"));
    let kills = kill_log::of(leader);
    assert_eq!(kills.len(), 1, "{kills:?}");
    assert!(
        kills[0].leader_unreaped,
        "killpg after the leader was reaped"
    );
    wait_dead(child, "descendant").await;
}

/// Leader exits normally and its descendant detached from the pipes: the
/// call returns promptly and the descendant must not outlive it.
#[tokio::test]
async fn normal_exit_still_cleans_up_lingering_descendants() {
    kill_log::enable();
    let d = tempfile::tempdir().unwrap();
    let p = d.path().display();
    let t = Instant::now();
    let r = sh(
        format!(
            "echo $$ > '{p}/leader'; sleep 30 >/dev/null 2>&1 </dev/null & echo $! > '{p}/child'; exit 0"
        ),
        10_000,
    )
    .await
    .unwrap();
    assert_eq!(r.code, Some(0));
    assert!(t.elapsed() < Duration::from_secs(5));
    let (leader, child) = (pidfile(d.path(), "leader"), pidfile(d.path(), "child"));
    assert!(kill_log::of(leader).iter().all(|k| k.leader_unreaped));
    wait_dead(child, "descendant").await;
}

#[tokio::test]
async fn cancellation_signals_the_group_while_the_leader_is_unreaped() {
    kill_log::enable();
    let d = tempfile::tempdir().unwrap();
    let p = d.path().display().to_string();
    let script = format!("echo $$ > '{p}/leader'; sleep 30 & echo $! > '{p}/child'; wait");
    let task = tokio::spawn(async move { sh(script, 60_000).await });
    for _ in 0..100 {
        if d.path().join("child").exists() {
            break;
        }
        tokio::time::sleep(Duration::from_millis(20)).await;
    }
    tokio::time::sleep(Duration::from_millis(100)).await;
    task.abort();
    let _ = task.await;
    let (leader, child) = (pidfile(d.path(), "leader"), pidfile(d.path(), "child"));
    let kills = kill_log::of(leader);
    assert_eq!(kills.len(), 1, "{kills:?}");
    assert!(kills[0].leader_unreaped);
    wait_dead(child, "descendant").await;
    wait_dead(leader, "leader").await;
}

/// Exit status survives the group kill that follows it.
#[tokio::test]
async fn exit_code_and_output_are_preserved() {
    let r = sh("echo out; echo err >&2; exit 3".into(), 5000)
        .await
        .unwrap();
    assert_eq!(
        (r.code, r.stdout.as_slice(), r.stderr.as_slice()),
        (Some(3), &b"out\n"[..], &b"err\n"[..])
    );
}

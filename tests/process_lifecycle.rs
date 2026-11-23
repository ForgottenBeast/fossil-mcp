//! Child-process lifecycle: stdin transport, deadlines, cancellation, output caps.
mod common;
use common::{FakeFossil, bound, is_error, wargs};
use fossil_mcp::Limits;
use fossil_mcp::server::types::Publication;
use std::time::Duration;

fn pid_alive(pid: u32) -> bool {
    std::fs::read_to_string(format!("/proc/{pid}/stat"))
        .map(|s| !s.contains(") Z "))
        .unwrap_or(false)
}

async fn assert_reaped(f: &FakeFossil, sub: &str) {
    assert_gone(f, &format!("pid.{sub}")).await;
}

async fn assert_gone(f: &FakeFossil, pidfile: &str) {
    let sub = pidfile;
    let pid: u32 = std::fs::read_to_string(f.file(pidfile))
        .unwrap()
        .trim()
        .parse()
        .unwrap();
    for _ in 0..60 {
        if !pid_alive(pid) {
            return;
        }
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    panic!("child {pid} ({sub}) still alive");
}

#[tokio::test]
async fn write_uses_stdin_not_page_path() {
    let f = FakeFossil::new();
    let w = bound(&f, |_| {}).await;
    let content = "line1\n\u{0}bytes \u{fc}n\u{ef}\n".repeat(50_000); // > pipe buffer
    let r = w
        .write_wiki_page(wargs("op1", "A/B", &content, Publication::LocalOnly))
        .await
        .unwrap();
    assert!(!is_error(&r));
    let calls = f.calls_to("create");
    assert_eq!(calls.len(), 1, "one create call expected");
    let (argv, stdin) = &calls[0];
    assert!(
        argv.iter()
            .all(|a| !a.contains("fossil_wiki_") && !a.ends_with(".txt")),
        "argv must carry no content file: {argv:?}"
    );
    assert_eq!(stdin, content.as_bytes(), "stdin must carry exact bytes");
}

#[tokio::test]
async fn timeout_reaps_child() {
    let f = FakeFossil::new();
    f.on("create", "echo ready > \"$D/ready\"; exec sleep 30");
    let w = bound(&f, |c| {
        c.limits = Limits {
            deadline: Duration::from_millis(400),
            ..Limits::default()
        }
    })
    .await;
    let r = tokio::time::timeout(
        Duration::from_secs(5),
        w.write_wiki_page(wargs("op1", "P", "x", Publication::LocalOnly)),
    )
    .await
    .expect("write must honour its own deadline, not hang")
    .unwrap();
    assert!(is_error(&r), "timeout is not success");
    assert_reaped(&f, "create").await;
}

#[tokio::test]
async fn cancel_reaps_child() {
    let f = FakeFossil::new();
    f.on("create", "echo ready > \"$D/ready\"; exec sleep 30");
    let w = bound(&f, |_| {}).await;
    let w2 = w.clone();
    let h = tokio::spawn(async move {
        w2.write_wiki_page(wargs("op1", "P", "x", Publication::LocalOnly))
            .await
    });
    for _ in 0..100 {
        if f.file("ready").exists() {
            break;
        }
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    assert!(f.file("ready").exists(), "child never signalled readiness");
    h.abort();
    let _ = h.await;
    assert_reaped(&f, "create").await;
}

#[tokio::test]
async fn stdout_limit_reaps_child() {
    let f = FakeFossil::new();
    let w = bound(&f, |c| {
        c.limits = Limits {
            deadline: Duration::from_secs(5),
            stdout_max: 4096,
            ..Limits::default()
        };
        c.allow_local_writes = false;
        c.state_dir = None;
    })
    .await;
    f.on(
        "list",
        "yes 0123456789abcdef | head -c 3000000; exec sleep 30",
    );
    let r = tokio::time::timeout(Duration::from_secs(4), w.list_wiki_pages())
        .await
        .expect("must stop reading at the cap");
    assert!(r.is_err(), "oversized output must be an error");
    assert_reaped(&f, "list").await;
}

/// The child forks a descendant that holds the pipes and outlives it.
const FORKING: &str = "sleep 30 & echo $! > \"$D/desc.pid\"; echo ready > \"$D/ready\"; wait";

#[tokio::test]
async fn timeout_kills_descendants() {
    let f = FakeFossil::new();
    f.on("create", FORKING);
    let w = bound(&f, |c| {
        c.limits = Limits {
            deadline: Duration::from_millis(500),
            ..Limits::default()
        }
    })
    .await;
    let r = tokio::time::timeout(
        Duration::from_secs(5),
        w.write_wiki_page(wargs("op1", "P", "x", Publication::LocalOnly)),
    )
    .await
    .expect("deadline honoured")
    .unwrap();
    assert!(is_error(&r));
    assert_gone(&f, "desc.pid").await;
}

#[tokio::test]
async fn cancel_kills_descendants() {
    let f = FakeFossil::new();
    f.on("create", FORKING);
    let w = bound(&f, |_| {}).await;
    let w2 = w.clone();
    let h = tokio::spawn(async move {
        w2.write_wiki_page(wargs("op1", "P", "x", Publication::LocalOnly))
            .await
    });
    for _ in 0..100 {
        if f.file("ready").exists() {
            break;
        }
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    assert!(f.file("ready").exists(), "child never signalled readiness");
    h.abort();
    let _ = h.await;
    assert_gone(&f, "desc.pid").await;
}

#[tokio::test]
async fn output_limit_kills_descendants() {
    let f = FakeFossil::new();
    let w = bound(&f, |c| {
        c.limits = Limits {
            deadline: Duration::from_secs(5),
            stdout_max: 4096,
            ..Limits::default()
        };
        c.allow_local_writes = false;
        c.state_dir = None;
    })
    .await;
    f.on(
        "list",
        "sleep 30 & echo $! > \"$D/desc.pid\"; yes 0123456789abcdef | head -c 3000000; wait",
    );
    let r = tokio::time::timeout(Duration::from_secs(4), w.list_wiki_pages())
        .await
        .expect("must stop reading at the cap");
    assert!(r.is_err());
    assert_gone(&f, "desc.pid").await;
}

//! Child-process lifecycle: stdin transport, deadlines, cancellation, output caps.
mod common;
use common::FakeFossil;
use fossil_mcp::{FossilWiki, Limits, WriteWikiPageArgs};
use rmcp::handler::server::wrapper::Parameters;
use std::time::Duration;

fn wiki(f: &FakeFossil, limits: Limits) -> FossilWiki {
    FossilWiki::new(Some(f.repo_file()))
        .with_fossil_bin(&f.bin)
        .with_limits(limits)
}

fn args(page: &str, content: &str) -> Parameters<WriteWikiPageArgs> {
    Parameters(WriteWikiPageArgs {
        page_name: page.into(),
        content: content.into(),
        mimetype: None,
        skip_sync: true,
        force_write: false,
    })
}

fn pid_alive(pid: u32) -> bool {
    std::fs::read_to_string(format!("/proc/{pid}/stat"))
        .map(|s| !s.contains(") Z "))
        .unwrap_or(false)
}

#[tokio::test]
async fn write_uses_stdin_not_page_path() {
    let f = FakeFossil::new();
    let w = wiki(&f, Limits::default());
    let content = "line1\n\u{0}bytes ünï\n".repeat(50_000); // > pipe buffer
    let _ = w.write_wiki_page(args("A/B", &content)).await;
    let calls = f.calls_to("create");
    assert_eq!(calls.len(), 1, "one create call expected");
    let (argv, stdin) = &calls[0];
    assert!(
        argv.iter().all(|a| !a.contains("fossil_wiki_") && !a.ends_with(".txt")),
        "argv must carry no content file: {argv:?}"
    );
    assert_eq!(stdin, content.as_bytes(), "stdin must carry exact bytes");
}

#[tokio::test]
async fn timeout_reaps_child() {
    let f = FakeFossil::new();
    f.on("create", "echo ready > \"$D/ready\"; exec sleep 30");
    let w = wiki(
        &f,
        Limits { deadline: Duration::from_millis(400), ..Limits::default() },
    );
    let started = std::time::Instant::now();
    let r = tokio::time::timeout(Duration::from_secs(5), w.write_wiki_page(args("P", "x")))
        .await
        .expect("write must honour its own deadline, not hang");
    assert!(started.elapsed() < Duration::from_secs(5));
    assert!(r.is_err(), "timeout is not success");
    let pid: u32 = std::fs::read_to_string(f.file("pid.create")).unwrap().trim().parse().unwrap();
    for _ in 0..40 {
        if !pid_alive(pid) {
            return;
        }
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    panic!("child {pid} still alive after timeout");
}

#[tokio::test]
async fn cancel_reaps_child() {
    let f = FakeFossil::new();
    f.on("create", "echo ready > \"$D/ready\"; exec sleep 30");
    let w = wiki(&f, Limits::default());
    let w2 = w.clone();
    let h = tokio::spawn(async move { w2.write_wiki_page(args("P", "x")).await });
    for _ in 0..100 {
        if f.file("ready").exists() {
            break;
        }
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    assert!(f.file("ready").exists(), "child never signalled readiness");
    h.abort();
    let _ = h.await;
    let pid: u32 = std::fs::read_to_string(f.file("pid.create")).unwrap().trim().parse().unwrap();
    for _ in 0..60 {
        if !pid_alive(pid) {
            return;
        }
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    panic!("child {pid} survived cancellation");
}

#[tokio::test]
async fn stdout_limit_reaps_child() {
    let f = FakeFossil::new();
    f.on("list", "yes 0123456789abcdef | head -c 3000000; exec sleep 30");
    let w = wiki(
        &f,
        Limits { deadline: Duration::from_secs(5), stdout_max: 4096, ..Limits::default() },
    );
    let r = tokio::time::timeout(Duration::from_secs(4), w.list_wiki_pages())
        .await
        .expect("must stop reading at the cap");
    assert!(r.is_err(), "oversized output must be an error");
    let pid: u32 = std::fs::read_to_string(f.file("pid.list")).unwrap().trim().parse().unwrap();
    for _ in 0..40 {
        if !pid_alive(pid) {
            return;
        }
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    panic!("child {pid} alive after output cap");
}

//! Black-box tests of the real binary over stdio: startup validation, the
//! stable tool catalog, retired tools, schemas, and partial outcomes.
mod common;
use common::{isolated_fossil, real_repo};
use serde_json::{Value, json};
use std::path::Path;
use std::process::Stdio;
use std::time::Duration;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::process::{Child, ChildStdin, ChildStdout, Command};

const BIN: &str = env!("CARGO_BIN_EXE_fossil-mcp");

struct Client {
    _child: Child,
    stdin: ChildStdin,
    out: BufReader<ChildStdout>,
    next: u64,
}

impl Client {
    async fn start(args: &[&str]) -> Self {
        let mut child = Command::new(BIN)
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .kill_on_drop(true)
            .spawn()
            .expect("spawn fossil-mcp");
        let stdin = child.stdin.take().unwrap();
        let out = BufReader::new(child.stdout.take().unwrap());
        let mut c = Self {
            _child: child,
            stdin,
            out,
            next: 1,
        };
        let init = c
            .request(
                "initialize",
                json!({"protocolVersion":"2025-03-26","capabilities":{},
                       "clientInfo":{"name":"t","version":"0"}}),
            )
            .await;
        assert!(init.get("result").is_some(), "initialize failed: {init}");
        c.notify("notifications/initialized").await;
        c
    }

    async fn send(&mut self, v: Value) {
        let mut line = v.to_string();
        line.push('\n');
        self.stdin.write_all(line.as_bytes()).await.unwrap();
        self.stdin.flush().await.unwrap();
    }

    async fn notify(&mut self, method: &str) {
        self.send(json!({"jsonrpc":"2.0","method":method})).await;
    }

    async fn request(&mut self, method: &str, params: Value) -> Value {
        let id = self.next;
        self.next += 1;
        self.send(json!({"jsonrpc":"2.0","id":id,"method":method,"params":params}))
            .await;
        loop {
            let mut line = String::new();
            let n = tokio::time::timeout(Duration::from_secs(20), self.out.read_line(&mut line))
                .await
                .expect("timed out waiting for reply")
                .unwrap();
            assert!(n > 0, "server closed stdout");
            // stdout must carry only JSON-RPC
            let v: Value = serde_json::from_str(line.trim()).expect("stdout line is JSON");
            if v.get("id") == Some(&json!(id)) {
                return v;
            }
        }
    }

    async fn tools(&mut self) -> Vec<Value> {
        let r = self.request("tools/list", json!({})).await;
        r["result"]["tools"].as_array().unwrap().clone()
    }

    async fn call(&mut self, name: &str, args: Value) -> Value {
        self.request("tools/call", json!({"name":name,"arguments":args}))
            .await
    }
}

fn names(tools: &[Value]) -> Vec<String> {
    let mut n: Vec<String> = tools
        .iter()
        .map(|t| t["name"].as_str().unwrap().to_string())
        .collect();
    n.sort();
    n
}

fn args_for(repo: &Path, bin: &Path, extra: &[&str]) -> Vec<String> {
    let mut a: Vec<String> = vec![
        "--repo-id".into(),
        "stdio".into(),
        "-R".into(),
        repo.display().to_string(),
        "--fossil-bin".into(),
        bin.display().to_string(),
    ];
    a.extend(extra.iter().map(|s| s.to_string()));
    a
}

async fn start_with(repo: &Path, bin: &Path, extra: &[&str]) -> Client {
    let a = args_for(repo, bin, extra);
    let refs: Vec<&str> = a.iter().map(String::as_str).collect();
    Client::start(&refs).await
}

async fn exit_status(args: &[&str]) -> (bool, Vec<u8>) {
    let out = tokio::time::timeout(
        Duration::from_secs(10),
        Command::new(BIN).args(args).stdin(Stdio::null()).output(),
    )
    .await
    .expect("binary must exit on invalid startup, not serve")
    .unwrap();
    (out.status.success(), out.stdout)
}

#[tokio::test]
async fn startup_requires_binding() {
    let (ok, stdout) = exit_status(&[]).await;
    assert!(!ok, "no-args start must fail");
    assert!(stdout.is_empty(), "nothing on stdout before MCP init");
    let (_repo, _bin, dir) = real_repo();
    let (ok, _) = exit_status(&["-R", "x"]).await;
    assert!(!ok, "alias is mandatory");
    let _ = dir;
}

#[tokio::test]
async fn startup_rejects_invalid_repository_files() {
    let (_repo, bin, dir) = real_repo();
    let empty = dir.path().join("empty.fossil");
    std::fs::write(&empty, b"").unwrap();
    let junk = dir.path().join("junk.fossil");
    std::fs::write(&junk, b"not a repo").unwrap();
    for bad in [
        empty,
        junk,
        dir.path().to_path_buf(),
        dir.path().join("missing"),
    ] {
        let a = args_for(&bad, &bin, &[]);
        let refs: Vec<&str> = a.iter().map(String::as_str).collect();
        let (ok, stdout) = exit_status(&refs).await;
        assert!(!ok, "{bad:?} must be rejected");
        assert!(stdout.is_empty());
    }
    let a = args_for(
        &dir.path().join("test.fossil"),
        &bin,
        &["--allow-local-writes"],
    );
    let refs: Vec<&str> = a.iter().map(String::as_str).collect();
    assert!(!exit_status(&refs).await.0, "writes need --state-dir");
}

#[tokio::test]
async fn catalog_is_stable_and_credential_free() {
    let (repo, bin, _dir) = real_repo();
    let mut c = start_with(&repo, &bin, &[]).await;
    let tools = c.tools().await;
    let expected = [
        "list_wiki_pages",
        "read_wiki_page",
        "wiki_operation_status",
        "wiki_reconcile_operation",
        "write_wiki_page",
    ];
    assert_eq!(names(&tools), expected);
    let schemas = serde_json::to_string(
        &tools
            .iter()
            .map(|t| (&t["inputSchema"], &t["outputSchema"]))
            .collect::<Vec<_>>(),
    )
    .unwrap();
    for banned in [
        "password",
        "api_key",
        "session_token",
        "repo_path",
        "force_write",
        "skip_sync",
    ] {
        assert!(!schemas.contains(banned), "schema leaks {banned}");
    }
    // Retired tools are not routable even by direct call; values are not echoed.
    for (name, args) in [
        ("configure_repository", json!({"repo_path":"SENTINEL-PATH"})),
        (
            "authenticate_wiki",
            json!({"username":"u","password":"SENTINEL-PW"}),
        ),
        ("search_wiki", json!({"query":"q","api_key":"SENTINEL-KEY"})),
    ] {
        let r = c.call(name, args).await;
        assert!(r.get("error").is_some(), "{name} must not dispatch: {r}");
        assert!(!r.to_string().contains("SENTINEL"), "echoed: {r}");
    }
    // Legacy fields on live tools are rejected without echo; catalog unchanged.
    let r = c
        .call(
            "read_wiki_page",
            json!({"page_name":"P","repo_path":"SENTINEL-PATH"}),
        )
        .await;
    assert!(!r.to_string().contains("SENTINEL"), "{r}");
    let r = c
        .call(
            "write_wiki_page",
            json!({"operation_id":"o","page_name":"P","content":"c","force_write":true}),
        )
        .await;
    assert!(
        r.get("error").is_some() || r["result"]["isError"] == json!(true),
        "{r}"
    );
    assert_eq!(names(&c.tools().await), expected, "catalog never changes");
}

#[tokio::test]
async fn tool_annotations_declare_read_only_and_mutating_tools() {
    let (repo, bin, _dir) = real_repo();
    let mut c = start_with(&repo, &bin, &[]).await;
    let tools = c.tools().await;
    // name -> (readOnlyHint, destructiveHint, idempotentHint, openWorldHint)
    // Writes only append Fossil artifacts (history is kept), so none is
    // destructive; write and reconcile may sync, so they reach the open world.
    let expected = [
        ("list_wiki_pages", (true, false, true, false)),
        ("read_wiki_page", (true, false, true, false)),
        ("wiki_operation_status", (true, false, true, false)),
        ("wiki_reconcile_operation", (false, false, true, true)),
        ("write_wiki_page", (false, false, true, true)),
    ];
    for (name, (ro, destructive, idempotent, open)) in expected {
        let t = tools.iter().find(|t| t["name"] == name).unwrap();
        let a = &t["annotations"];
        assert_eq!(a["readOnlyHint"], json!(ro), "{name} readOnlyHint: {a}");
        assert_eq!(a["destructiveHint"], json!(destructive), "{name}: {a}");
        assert_eq!(a["idempotentHint"], json!(idempotent), "{name}: {a}");
        assert_eq!(a["openWorldHint"], json!(open), "{name}: {a}");
    }
}

#[tokio::test]
async fn read_only_mode_denies_writes_but_keeps_catalog() {
    let (repo, bin, _dir) = real_repo();
    let mut c = start_with(&repo, &bin, &[]).await;
    let r = c
        .call(
            "write_wiki_page",
            json!({"operation_id":"o","page_name":"P","content":"c"}),
        )
        .await;
    assert_eq!(r["result"]["isError"], json!(true));
    assert_eq!(
        r["result"]["structuredContent"]["error_code"],
        json!("write_disabled")
    );
    let r = c
        .call("wiki_operation_status", json!({"operation_id":"o"}))
        .await;
    assert_eq!(
        r["result"]["structuredContent"]["error_code"],
        json!("write_disabled")
    );
    let r = c.call("list_wiki_pages", json!({})).await;
    assert_eq!(r["result"]["structuredContent"]["pages"], json!([]));
}

#[tokio::test]
async fn write_read_and_partial_outcome_over_stdio() {
    let (repo, bin, dir) = real_repo();
    let state = dir.path().join("state");
    let state = state.to_str().unwrap();
    let mut c = start_with(
        &repo,
        &bin,
        &[
            "--allow-local-writes",
            "--allow-repository-sync",
            "--state-dir",
            state,
        ],
    )
    .await;

    let r = c
        .call(
            "write_wiki_page",
            json!({"operation_id":"op-1","page_name":"Home","content":"hello","mimetype":"text/x-markdown"}),
        )
        .await;
    assert_eq!(r["result"]["isError"], json!(false), "{r}");
    let rc = &r["result"]["structuredContent"]["receipt"];
    assert_eq!(rc["commit_state"], json!("committed"));
    assert_eq!(rc["publication_state"], json!("not_requested"));
    let rev = rc["revision"].as_str().unwrap().to_string();
    assert_eq!(rc["repo_id"], json!("stdio"));

    let r = c.call("read_wiki_page", json!({"page_name":"Home"})).await;
    assert_eq!(r["result"]["structuredContent"]["content"], json!("hello"));
    assert_eq!(r["result"]["structuredContent"]["revision"], json!(rev));

    // Partial outcome: committed locally, no remote configured.
    let r = c
        .call(
            "write_wiki_page",
            json!({"operation_id":"op-2","page_name":"Home","content":"v2","publication":"sync_repository"}),
        )
        .await;
    assert_eq!(r["result"]["isError"], json!(true));
    let rc = &r["result"]["structuredContent"]["receipt"];
    assert_eq!(rc["commit_state"], json!("committed"));
    assert_eq!(rc["publication_state"], json!("pending"));
    assert_eq!(rc["error_code"], json!("no_remote"));
    assert_eq!(rc["previous_revision"], json!(rev));
    // text content carries the same receipt as the structured result
    let text: Value =
        serde_json::from_str(r["result"]["content"][0]["text"].as_str().unwrap()).unwrap();
    assert_eq!(&text["receipt"], rc);
    let wire = r.to_string();
    assert!(
        !wire.contains(dir.path().to_str().unwrap()),
        "no filesystem paths on the wire"
    );

    // Replay after a "lost reply": same receipt, no second commit.
    let again = c
        .call(
            "write_wiki_page",
            json!({"operation_id":"op-2","page_name":"Home","content":"v2","publication":"sync_repository"}),
        )
        .await;
    assert_eq!(
        again["result"]["structuredContent"],
        r["result"]["structuredContent"]
    );
    let r = c
        .call("wiki_operation_status", json!({"operation_id":"op-2"}))
        .await;
    assert_eq!(r["result"]["structuredContent"]["receipt"], *rc);
}

#[tokio::test]
async fn packaged_style_launch_with_empty_path_uses_fossil_bin() {
    // The binary must not need PATH: an absolute --fossil-bin is enough.
    let dir = tempfile::tempdir().unwrap();
    let bin = isolated_fossil(dir.path());
    let repo = dir.path().join("r.fossil");
    assert!(
        std::process::Command::new(&bin)
            .arg("new")
            .arg(&repo)
            .output()
            .unwrap()
            .status
            .success()
    );
    let a = args_for(&repo, &bin, &[]);
    let mut child = Command::new(BIN)
        .args(&a)
        .env_clear()
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .kill_on_drop(true)
        .spawn()
        .unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let mut out = BufReader::new(child.stdout.take().unwrap());
    stdin
        .write_all(
            b"{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"protocolVersion\":\"2025-03-26\",\"capabilities\":{},\"clientInfo\":{\"name\":\"t\",\"version\":\"0\"}}}\n",
        )
        .await
        .unwrap();
    let mut line = String::new();
    tokio::time::timeout(Duration::from_secs(10), out.read_line(&mut line))
        .await
        .unwrap()
        .unwrap();
    assert!(line.contains("\"result\""), "{line}");
}

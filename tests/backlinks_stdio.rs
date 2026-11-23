//! Black-box tests of the real binary: the `wiki_backlinks` tool is only in
//! the catalog when the whole flag group is supplied, carries the exact
//! annotations and schema, and neither stderr nor any tool result ever
//! contains the token, the key material or the key file path.
mod common;
mod fake_http;

use common::real_repo;
use fake_http::{Fake, Reply};
use serde_json::{Value, json};
use std::os::unix::fs::PermissionsExt;
use std::path::Path;
use std::process::Stdio;
use std::time::Duration;
use tokio::io::{AsyncBufReadExt, AsyncReadExt, AsyncWriteExt, BufReader};
use tokio::process::{Child, ChildStderr, ChildStdin, ChildStdout, Command};

const BIN: &str = env!("CARGO_BIN_EXE_fossil-mcp");
const PRIVATE_PEM: &str = include_str!("fixtures/test-rsa-private.pem");
const TOKEN: &str = "SENTINEL-ACCESS-TOKEN-0123456789";

struct Client {
    child: Child,
    stdin: ChildStdin,
    out: BufReader<ChildStdout>,
    err: ChildStderr,
    next: u64,
}

impl Client {
    async fn start(args: &[String]) -> Self {
        let mut child = Command::new(BIN)
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .kill_on_drop(true)
            .spawn()
            .expect("spawn");
        let stdin = child.stdin.take().unwrap();
        let out = BufReader::new(child.stdout.take().unwrap());
        let err = child.stderr.take().unwrap();
        let mut c = Self {
            child,
            stdin,
            out,
            err,
            next: 1,
        };
        let init = c
            .request(
                "initialize",
                json!({"protocolVersion":"2025-03-26","capabilities":{},
                       "clientInfo":{"name":"t","version":"0"}}),
            )
            .await;
        assert!(init.get("result").is_some(), "{init}");
        c.send(json!({"jsonrpc":"2.0","method":"notifications/initialized"}))
            .await;
        c
    }

    async fn send(&mut self, v: Value) {
        let mut line = v.to_string();
        line.push('\n');
        self.stdin.write_all(line.as_bytes()).await.unwrap();
        self.stdin.flush().await.unwrap();
    }

    async fn request(&mut self, method: &str, params: Value) -> Value {
        let id = self.next;
        self.next += 1;
        self.send(json!({"jsonrpc":"2.0","id":id,"method":method,"params":params}))
            .await;
        loop {
            let mut line = String::new();
            let n = tokio::time::timeout(Duration::from_secs(30), self.out.read_line(&mut line))
                .await
                .expect("reply timeout")
                .unwrap();
            assert!(n > 0, "server closed stdout");
            let v: Value = serde_json::from_str(line.trim()).expect("JSON line");
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

    /// Stop the child and return everything it wrote to stderr.
    async fn stderr(mut self) -> String {
        let _ = self.child.kill().await;
        let mut s = String::new();
        let _ = self.err.read_to_string(&mut s).await;
        s
    }
}

fn base_args(repo: &Path, bin: &Path) -> Vec<String> {
    vec![
        "--repo-id".into(),
        "stdio".into(),
        "-R".into(),
        repo.display().to_string(),
        "--fossil-bin".into(),
        bin.display().to_string(),
    ]
}

fn group(url: &str, issuer: &str, key: &Path) -> Vec<String> {
    vec![
        "--backlinks-url".into(),
        url.into(),
        "--backlinks-issuer".into(),
        issuer.into(),
        "--backlinks-key-file".into(),
        key.display().to_string(),
        "--backlinks-audience-scope".into(),
        "urn:zitadel:iam:org:project:id:42:aud".into(),
    ]
}

fn names(tools: &[Value]) -> Vec<String> {
    let mut n: Vec<String> = tools
        .iter()
        .map(|t| t["name"].as_str().unwrap().to_string())
        .collect();
    n.sort();
    n
}

async fn exits_nonzero(args: &[String]) -> bool {
    let out = tokio::time::timeout(
        Duration::from_secs(10),
        Command::new(BIN).args(args).stdin(Stdio::null()).output(),
    )
    .await
    .expect("must exit, not serve")
    .unwrap();
    assert!(out.stdout.is_empty());
    !out.status.success()
}

fn key_file(dir: &Path) -> std::path::PathBuf {
    let p = dir.join("SENTINEL-KEYFILE-NAME.json");
    std::fs::write(
        &p,
        json!({"type":"serviceaccount","keyId":"k1","key":PRIVATE_PEM,"userId":"u1"}).to_string(),
    )
    .unwrap();
    std::fs::set_permissions(&p, std::fs::Permissions::from_mode(0o600)).unwrap();
    p
}

fn fakes() -> (Fake, Fake) {
    let issuer =
        Fake::start(|_, _| Reply::json(200, json!({"access_token": TOKEN, "expires_in": 3600})));
    let sidecar = Fake::start(|req, _| {
        if req.header("authorization") != Some(&format!("Bearer {TOKEN}")) {
            return Reply::json(401, json!({}));
        }
        Reply::json(
            200,
            json!({"schema_version":"backlinks.v1","repo_id":"stdio","page":"Home",
                   "status":"current","checked_at":"2026-11-23T10:00:00Z","generation":3,
                   "inbound":[{"source_page":"A"},{"source_page":"B"}]}),
        )
    });
    (issuer, sidecar)
}

const EXPECTED_WITHOUT: [&str; 5] = [
    "list_wiki_pages",
    "read_wiki_page",
    "wiki_operation_status",
    "wiki_reconcile_operation",
    "write_wiki_page",
];

#[tokio::test]
async fn tool_is_absent_without_the_flag_group() {
    let (repo, bin, _dir) = real_repo();
    let mut c = Client::start(&base_args(&repo, &bin)).await;
    assert_eq!(names(&c.tools().await), EXPECTED_WITHOUT);
    let r = c.call("wiki_backlinks", json!({"page":"Home"})).await;
    assert!(r.get("error").is_some(), "must not dispatch: {r}");
}

#[tokio::test]
async fn partial_flag_groups_are_rejected_at_startup() {
    let (repo, bin, dir) = real_repo();
    let key = key_file(dir.path());
    let full = group("https://sidecar.example", "https://issuer.example", &key);
    // Dropping any one flag (with its value) must fail startup.
    for skip in 0..4 {
        let mut a = base_args(&repo, &bin);
        for (i, pair) in full.chunks(2).enumerate() {
            if i != skip {
                a.extend(pair.iter().cloned());
            }
        }
        assert!(exits_nonzero(&a).await, "missing flag #{skip} must fail");
    }
    // The timeout alone is also a partial group.
    let mut a = base_args(&repo, &bin);
    a.extend(["--backlinks-timeout-ms".into(), "5000".into()]);
    assert!(exits_nonzero(&a).await);
}

#[tokio::test]
async fn invalid_flag_values_are_rejected_at_startup() {
    let (repo, bin, dir) = real_repo();
    let key = key_file(dir.path());
    for (url, issuer, timeout) in [
        ("http://sidecar.example", "https://issuer.example", "10000"),
        (
            "https://sidecar.example/v1",
            "https://issuer.example",
            "10000",
        ),
        ("https://sidecar.example", "http://issuer.example", "10000"),
        ("https://sidecar.example", "https://issuer.example", "999"),
        ("https://sidecar.example", "https://issuer.example", "60001"),
    ] {
        let mut a = base_args(&repo, &bin);
        a.extend(group(url, issuer, &key));
        a.extend(["--backlinks-timeout-ms".into(), timeout.into()]);
        assert!(exits_nonzero(&a).await, "{url} {issuer} {timeout}");
    }
}

#[tokio::test]
async fn catalog_with_the_group_adds_exactly_one_read_only_tool() {
    let (repo, bin, dir) = real_repo();
    let key = key_file(dir.path());
    let (issuer, sidecar) = fakes();
    let mut a = base_args(&repo, &bin);
    a.extend(group(&sidecar.url(), &issuer.url(), &key));
    let mut c = Client::start(&a).await;
    let tools = c.tools().await;
    let mut want: Vec<&str> = EXPECTED_WITHOUT.to_vec();
    want.push("wiki_backlinks");
    want.sort();
    assert_eq!(names(&tools), want);

    let t = tools
        .iter()
        .find(|t| t["name"] == "wiki_backlinks")
        .unwrap();
    let ann = &t["annotations"];
    assert_eq!(ann["readOnlyHint"], json!(true));
    assert_eq!(ann["destructiveHint"], json!(false));
    assert_eq!(ann["idempotentHint"], json!(true));
    assert_eq!(ann["openWorldHint"], json!(true));

    // Schema snapshot: closed input object with exactly these properties.
    let input = &t["inputSchema"];
    assert_eq!(input["additionalProperties"], json!(false), "{input}");
    let props: Vec<&str> = {
        let mut p: Vec<&str> = input["properties"]
            .as_object()
            .unwrap()
            .keys()
            .map(String::as_str)
            .collect();
        p.sort();
        p
    };
    assert_eq!(props, ["cursor", "limit", "page"]);
    assert_eq!(input["required"], json!(["page"]));
    let out = &t["outputSchema"]["properties"];
    let mut keys: Vec<&str> = out
        .as_object()
        .unwrap()
        .keys()
        .map(String::as_str)
        .collect();
    keys.sort();
    assert_eq!(
        keys,
        [
            "checked_at",
            "generation",
            "inbound",
            "next_cursor",
            "page",
            "repo_id",
            "schema_version",
            "status",
            "total_inbound"
        ]
    );
    let schemas = serde_json::to_string(t).unwrap();
    for banned in ["token", "password", "api_key", "key_file", "issuer"] {
        assert!(!schemas.contains(banned), "schema leaks {banned}");
    }

    // Existing tools keep their annotations.
    for (name, open) in [("read_wiki_page", false), ("write_wiki_page", true)] {
        let t = tools.iter().find(|t| t["name"] == name).unwrap();
        assert_eq!(t["annotations"]["openWorldHint"], json!(open));
    }
}

#[tokio::test]
async fn call_over_stdio_works_and_leaks_no_secret() {
    let (repo, bin, dir) = real_repo();
    let key = key_file(dir.path());
    let (issuer, sidecar) = fakes();
    let mut a = base_args(&repo, &bin);
    a.extend(group(&sidecar.url(), &issuer.url(), &key));
    let mut c = Client::start(&a).await;

    let ok = c.call("wiki_backlinks", json!({"page":"Home"})).await;
    assert_eq!(ok["result"]["isError"], json!(false), "{ok}");
    let s = &ok["result"]["structuredContent"];
    assert_eq!(s["repo_id"], "stdio");
    assert_eq!(s["total_inbound"], 2);
    assert_eq!(
        s["inbound"],
        json!([{"source_page":"A"},{"source_page":"B"}])
    );
    assert_eq!(s["next_cursor"], Value::Null);

    // Failure paths: stale cursor, bad argument, sidecar 401 forever.
    let stale = c
        .call("wiki_backlinks", json!({"page":"Home","cursor":"1:0"}))
        .await;
    assert_eq!(stale["result"]["isError"], json!(true), "{stale}");
    let bad = c
        .call(
            "wiki_backlinks",
            json!({"page":"Home","token":"SENTINEL-ARG"}),
        )
        .await;
    assert!(!bad.to_string().contains("SENTINEL-ARG"), "{bad}");

    let mut wire = vec![ok.to_string(), stale.to_string(), bad.to_string()];
    let stderr = c.stderr().await;
    wire.push(stderr);
    for w in wire {
        for banned in [
            TOKEN,
            "PRIVATE KEY",
            "SENTINEL-KEYFILE-NAME",
            dir.path().to_str().unwrap(),
        ] {
            assert!(!w.contains(banned), "leaked {banned:?} in {w}");
        }
    }
}

#[tokio::test]
async fn credential_failure_over_stdio_is_fixed_and_pathless() {
    let (repo, bin, dir) = real_repo();
    let key = key_file(dir.path());
    std::fs::set_permissions(&key, std::fs::Permissions::from_mode(0o644)).unwrap();
    let (issuer, sidecar) = fakes();
    let mut a = base_args(&repo, &bin);
    a.extend(group(&sidecar.url(), &issuer.url(), &key));
    let mut c = Client::start(&a).await;
    let r = c.call("wiki_backlinks", json!({"page":"Home"})).await;
    assert_eq!(r["result"]["isError"], json!(true), "{r}");
    let text = r.to_string();
    assert!(text.contains("credential_unavailable"), "{text}");
    assert!(!text.contains("SENTINEL-KEYFILE-NAME"), "{text}");
    let stderr = c.stderr().await;
    assert!(!stderr.contains("SENTINEL-KEYFILE-NAME"), "{stderr}");
    assert_eq!(issuer.count() + sidecar.count(), 0);
}

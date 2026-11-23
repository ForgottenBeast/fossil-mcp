//! F2: the `wiki_backlinks` tool against a fake issuer and a fake sidecar.
mod common;
mod fake_http;

use common::{FakeFossil, bound};
use fake_http::{Fake, Reply, Req};
use fossil_mcp::server::backlinks::percent_encode;
use fossil_mcp::server::types::{Cursor, ErrorCode, WikiBacklinksArgs, WikiBacklinksResponse};
use fossil_mcp::{BacklinksConfig, FossilWiki};
use proptest::prelude::*;
use rmcp::handler::server::wrapper::Parameters;
use serde_json::{Value, json};
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

const PRIVATE_PEM: &str = include_str!("fixtures/test-rsa-private.pem");

struct Env {
    fossil: FakeFossil,
    issuer: Fake,
    sidecar: Fake,
    key_file: PathBuf,
}

fn issuer(expires_in: u64) -> Fake {
    Fake::start(move |_, idx| {
        Reply::json(
            200,
            json!({"access_token": format!("tok{}", idx + 1), "expires_in": expires_in}),
        )
    })
}

fn rows(n: usize) -> Value {
    Value::Array(
        (0..n)
            .map(|i| json!({"source_page": format!("Src{i:04}")}))
            .collect(),
    )
}

fn page_body(inbound: Value) -> Value {
    json!({"schema_version":"backlinks.v1","repo_id":"repo1","page":"Target","status":"current",
           "checked_at":"2026-11-23T10:00:00Z","generation":7,"inbound":inbound})
}

fn env(sidecar: impl Fn(&Req, usize) -> Reply + Send + Sync + 'static, expires_in: u64) -> Env {
    let fossil = FakeFossil::new();
    let key_file = fossil.dir.path().join("SENTINEL-PATH-key.json");
    std::fs::write(
        &key_file,
        json!({"type":"serviceaccount","keyId":"k1","key":PRIVATE_PEM,"userId":"u1"}).to_string(),
    )
    .unwrap();
    std::fs::set_permissions(&key_file, std::fs::Permissions::from_mode(0o600)).unwrap();
    Env {
        fossil,
        issuer: issuer(expires_in),
        sidecar: Fake::start(sidecar),
        key_file,
    }
}

async fn wiki(e: &Env, timeout_ms: u64) -> FossilWiki {
    let cfg = BacklinksConfig {
        url: e.sidecar.url(),
        issuer: e.issuer.url(),
        key_file: e.key_file.clone(),
        audience_scopes: vec!["urn:zitadel:iam:org:project:id:42:aud".into()],
        timeout: Duration::from_millis(timeout_ms),
    };
    bound(&e.fossil, move |c| c.backlinks = Some(cfg)).await
}

fn args(page: &str, cursor: Option<&str>, limit: Option<u32>) -> Parameters<WikiBacklinksArgs> {
    Parameters(WikiBacklinksArgs {
        page: page.into(),
        cursor: cursor.map(String::from),
        limit,
    })
}

async fn call(
    w: &FossilWiki,
    a: Parameters<WikiBacklinksArgs>,
) -> Result<WikiBacklinksResponse, String> {
    w.wiki_backlinks(a).await.map(|j| j.0)
}

fn code(e: ErrorCode) -> String {
    serde_json::to_value(e)
        .unwrap()
        .as_str()
        .unwrap()
        .to_string()
}

fn assert_code(r: Result<WikiBacklinksResponse, String>, want: ErrorCode) -> String {
    let err = r.expect_err("must fail");
    assert!(
        err.starts_with(&format!("{}: ", code(want))),
        "want {want:?}, got {err}"
    );
    err
}

// ---- success and pagination ----------------------------------------------------

#[tokio::test]
async fn paginates_250_rows_with_cursors_and_total() {
    let e = env(|_, _| Reply::json(200, page_body(rows(250))), 3600);
    let w = wiki(&e, 5000).await;

    let p1 = call(&w, args("Target", None, None)).await.unwrap();
    assert_eq!(p1.schema_version, "backlinks.v1");
    assert_eq!(p1.repo_id, "repo1");
    assert_eq!(p1.page, "Target");
    assert_eq!(p1.status, "current");
    assert_eq!(p1.checked_at, "2026-11-23T10:00:00Z");
    assert_eq!(p1.generation, 7);
    assert_eq!(p1.total_inbound, 250);
    assert_eq!(p1.inbound.len(), 100, "default limit is 100");
    assert_eq!(p1.next_cursor.as_deref(), Some("7:100"));

    let p2 = call(&w, args("Target", p1.next_cursor.as_deref(), None))
        .await
        .unwrap();
    assert_eq!(p2.inbound.len(), 100);
    assert_eq!(p2.next_cursor.as_deref(), Some("7:200"));
    let p3 = call(&w, args("Target", p2.next_cursor.as_deref(), None))
        .await
        .unwrap();
    assert_eq!(p3.inbound.len(), 50);
    assert_eq!(p3.next_cursor, None);

    let all: Vec<String> = [p1, p2, p3]
        .iter()
        .flat_map(|p| p.inbound.iter().map(|r| r.source_page.clone()))
        .collect();
    let want: Vec<String> = (0..250).map(|i| format!("Src{i:04}")).collect();
    assert_eq!(all, want);

    let small = call(&w, args("Target", None, Some(7))).await.unwrap();
    assert_eq!(small.inbound.len(), 7);
    assert_eq!(small.next_cursor.as_deref(), Some("7:7"));
    let last = call(&w, args("Target", Some("7:250"), Some(5)))
        .await
        .unwrap();
    assert!(last.inbound.is_empty() && last.next_cursor.is_none());
}

#[tokio::test]
async fn empty_inbound_is_a_success() {
    let e = env(|_, _| Reply::json(200, page_body(json!([]))), 3600);
    let w = wiki(&e, 5000).await;
    let r = call(&w, args("Target", None, None)).await.unwrap();
    assert_eq!(r.total_inbound, 0);
    assert!(r.inbound.is_empty() && r.next_cursor.is_none());
}

#[tokio::test]
async fn request_shape_encodes_the_page_and_sends_the_bearer() {
    let e = env(|_, _| Reply::json(200, page_body(json!([]))), 3600);
    let w = wiki(&e, 5000).await;
    let name = "Docs/API v2 & é=%?#";
    let mut body = page_body(json!([]));
    body["page"] = json!(name);
    let e2 = env(move |_, _| Reply::json(200, body.clone()), 3600);
    let w2 = wiki(&e2, 5000).await;
    call(&w2, args(name, None, None)).await.unwrap();
    let req = &e2.sidecar.requests()[0];
    assert_eq!(req.method, "GET");
    assert_eq!(
        req.target,
        format!("/v1/backlinks?name={}", percent_encode(name))
    );
    assert_eq!(req.header("authorization"), Some("Bearer tok1"));
    call(&w, args("Target", None, None)).await.unwrap();
    assert_eq!(e.sidecar.requests()[0].target, "/v1/backlinks?name=Target");
}

// ---- argument validation ------------------------------------------------------

#[tokio::test]
async fn invalid_arguments_never_reach_the_network() {
    let e = env(|_, _| Reply::json(200, page_body(rows(10))), 3600);
    let w = wiki(&e, 5000).await;
    for a in [
        args("", None, None),
        args("-R", None, None),
        args("a\nb", None, None),
        args(&"x".repeat(257), None, None),
        args("Target", None, Some(0)),
        args("Target", None, Some(201)),
        args("Target", Some("garbage"), None),
        args("Target", Some("7:"), None),
        args("Target", Some(":3"), None),
        args("Target", Some("7:3:1"), None),
        args("Target", Some("-1:3"), None),
    ] {
        assert_code(call(&w, a).await, ErrorCode::InvalidArgument);
    }
    assert_eq!(e.issuer.count() + e.sidecar.count(), 0);
}

#[tokio::test]
async fn offset_past_the_end_is_invalid() {
    let e = env(|_, _| Reply::json(200, page_body(rows(10))), 3600);
    let w = wiki(&e, 5000).await;
    assert_code(
        call(&w, args("Target", Some("7:11"), None)).await,
        ErrorCode::InvalidArgument,
    );
}

#[tokio::test]
async fn stale_cursor_is_cursor_stale() {
    let e = env(|_, _| Reply::json(200, page_body(rows(250))), 3600);
    let w = wiki(&e, 5000).await;
    assert_code(
        call(&w, args("Target", Some("6:100"), None)).await,
        ErrorCode::CursorStale,
    );
}

#[test]
fn unknown_input_fields_are_rejected() {
    for field in ["token", "url", "repo_id", "password"] {
        let j = format!(r#"{{"page":"P","{field}":"SENTINEL"}}"#);
        let err = serde_json::from_str::<WikiBacklinksArgs>(&j)
            .unwrap_err()
            .to_string();
        assert!(!err.contains("SENTINEL"), "{err}");
    }
    let a: WikiBacklinksArgs = serde_json::from_str(r#"{"page":"P"}"#).unwrap();
    assert_eq!((a.cursor, a.limit), (None, None));
}

// ---- sidecar status mapping ------------------------------------------------------

#[tokio::test]
async fn sidecar_statuses_map_to_fixed_codes() {
    let cases: [(u16, Value, ErrorCode); 5] = [
        (
            404,
            json!({"error":{"code":"NOT_FOUND_OR_DENIED"}}),
            ErrorCode::PageNotFound,
        ),
        (
            400,
            json!({"error":{"code":"INVALID_ARGUMENT"}}),
            ErrorCode::InvalidArgument,
        ),
        (403, json!({"error":"x"}), ErrorCode::BacklinksForbidden),
        (500, json!({}), ErrorCode::BacklinksUnreachable),
        (302, json!({}), ErrorCode::BadResponse),
    ];
    for (status, body, want) in cases {
        let e = env(move |_, _| Reply::json(status, body.clone()), 3600);
        let w = wiki(&e, 5000).await;
        assert_code(call(&w, args("Target", None, None)).await, want);
        assert_eq!(e.sidecar.count(), 1, "{status}: no retry");
    }
}

#[tokio::test]
async fn unavailable_index_carries_its_status() {
    for st in ["updating", "unavailable"] {
        let body = json!({"schema_version":"backlinks.v1","repo_id":"repo1","page":"Target",
            "status":st,"checked_at":null,"generation":0,"inbound":[],
            "error":{"code":"INDEX_UNAVAILABLE"}});
        let e = env(move |_, _| Reply::json(503, body.clone()), 3600);
        let w = wiki(&e, 5000).await;
        let err = assert_code(
            call(&w, args("Target", None, None)).await,
            ErrorCode::BacklinksUnavailable,
        );
        assert!(err.contains(st), "{err}");
    }
    // An unknown status string is not echoed.
    let e = env(
        |_, _| Reply::json(503, json!({"status":"SENTINEL-STATUS"})),
        3600,
    );
    let w = wiki(&e, 5000).await;
    let err = assert_code(
        call(&w, args("Target", None, None)).await,
        ErrorCode::BacklinksUnavailable,
    );
    assert!(!err.contains("SENTINEL"), "{err}");
}

#[tokio::test]
async fn bad_sidecar_documents_are_bad_response() {
    let mut wrong_version = page_body(json!([]));
    wrong_version["schema_version"] = json!("backlinks.v2");
    let mut not_current = page_body(json!([]));
    not_current["status"] = json!("updating");
    let mut other_page = page_body(json!([]));
    other_page["page"] = json!("Other");
    let mut no_generation = page_body(json!([]));
    no_generation.as_object_mut().unwrap().remove("generation");
    let mut bad_row = page_body(json!([{"nope": 1}]));
    bad_row["generation"] = json!(1);
    for doc in [
        wrong_version,
        not_current,
        other_page,
        no_generation,
        bad_row,
        json!("string"),
        json!([]),
    ] {
        let e = env(move |_, _| Reply::json(200, doc.clone()), 3600);
        let w = wiki(&e, 5000).await;
        assert_code(
            call(&w, args("Target", None, None)).await,
            ErrorCode::BadResponse,
        );
    }
    let e = env(
        |_, _| Reply::Full {
            status: 200,
            body: b"<html>not json</html>".to_vec(),
        },
        3600,
    );
    let w = wiki(&e, 5000).await;
    assert_code(
        call(&w, args("Target", None, None)).await,
        ErrorCode::BadResponse,
    );
}

#[tokio::test]
async fn repo_id_mismatch_is_surfaced() {
    let mut body = page_body(json!([]));
    body["repo_id"] = json!("the-other-wiki");
    let e = env(move |_, _| Reply::json(200, body.clone()), 3600);
    let w = wiki(&e, 5000).await;
    let err = assert_code(
        call(&w, args("Target", None, None)).await,
        ErrorCode::BacklinksRepoMismatch,
    );
    assert!(!err.contains("the-other-wiki"), "{err}");
}

#[tokio::test]
async fn oversized_body_is_bad_response() {
    let e = env(
        |_, _| Reply::Full {
            status: 200,
            body: vec![b'a'; 8 * 1024 * 1024 + 1024],
        },
        3600,
    );
    let w = wiki(&e, 10_000).await;
    assert_code(
        call(&w, args("Target", None, None)).await,
        ErrorCode::BadResponse,
    );
}

#[tokio::test]
async fn slow_body_times_out() {
    let e = env(
        |_, _| Reply::Stall {
            status: 200,
            stall: Duration::from_secs(5),
        },
        3600,
    );
    let w = wiki(&e, 1000).await;
    let t = std::time::Instant::now();
    assert_code(
        call(&w, args("Target", None, None)).await,
        ErrorCode::Timeout,
    );
    assert!(t.elapsed() < Duration::from_secs(4), "{:?}", t.elapsed());
}

#[tokio::test]
async fn unreachable_sidecar_is_unreachable() {
    let e = env(|_, _| Reply::json(200, page_body(json!([]))), 3600);
    let port = {
        let l = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
        l.local_addr().unwrap().port()
    };
    let cfg = BacklinksConfig {
        url: format!("http://127.0.0.1:{port}"),
        issuer: e.issuer.url(),
        key_file: e.key_file.clone(),
        audience_scopes: vec!["s".into()],
        timeout: Duration::from_millis(2000),
    };
    let w = bound(&e.fossil, move |c| c.backlinks = Some(cfg)).await;
    assert_code(
        call(&w, args("Target", None, None)).await,
        ErrorCode::BacklinksUnreachable,
    );
}

// ---- token sequencing --------------------------------------------------------

#[tokio::test]
async fn two_calls_use_one_token_request() {
    let e = env(|_, _| Reply::json(200, page_body(json!([]))), 3600);
    let w = wiki(&e, 5000).await;
    call(&w, args("Target", None, None)).await.unwrap();
    call(&w, args("Target", None, None)).await.unwrap();
    assert_eq!(e.issuer.count(), 1);
    assert_eq!(e.sidecar.count(), 2);
}

#[tokio::test]
async fn token_inside_the_refresh_margin_is_an_auth_failure() {
    // expires_in <= 60 s can never be cached: the issuer's policy is wrong,
    // and the sidecar is not called with a token that is about to expire.
    let e = env(|_, _| Reply::json(200, page_body(json!([]))), 60);
    let w = wiki(&e, 5000).await;
    assert_code(
        call(&w, args("Target", None, None)).await,
        ErrorCode::BacklinksAuthFailed,
    );
    assert_eq!(e.sidecar.count(), 0);
}

#[tokio::test]
async fn a_401_triggers_exactly_one_refresh_and_one_retry() {
    let e = env(
        |req, _| {
            if req.header("authorization") == Some("Bearer tok1") {
                Reply::json(401, json!({"error":"expired"}))
            } else {
                Reply::json(200, page_body(rows(3)))
            }
        },
        3600,
    );
    let w = wiki(&e, 5000).await;
    let r = call(&w, args("Target", None, None)).await.unwrap();
    assert_eq!(r.total_inbound, 3);
    assert_eq!(e.issuer.count(), 2, "one initial token, one refresh");
    assert_eq!(e.sidecar.count(), 2, "one rejected try, one retry");
    // The replacement is cached for later calls.
    call(&w, args("Target", None, None)).await.unwrap();
    assert_eq!(e.issuer.count(), 2);
}

#[tokio::test]
async fn a_persistent_401_is_auth_failed_after_one_retry() {
    let e = env(|_, _| Reply::json(401, json!({})), 3600);
    let w = wiki(&e, 5000).await;
    assert_code(
        call(&w, args("Target", None, None)).await,
        ErrorCode::BacklinksAuthFailed,
    );
    assert_eq!(e.issuer.count(), 2);
    assert_eq!(e.sidecar.count(), 2);
}

#[tokio::test]
async fn issuer_rejection_is_auth_failed_without_calling_the_sidecar() {
    let fossil = FakeFossil::new();
    let sidecar = Fake::start(|_, _| Reply::json(200, page_body(json!([]))));
    let issuer = Fake::start(|_, _| Reply::json(400, json!({"error":"invalid_grant"})));
    let key_file = fossil.dir.path().join("key.json");
    std::fs::write(
        &key_file,
        json!({"type":"serviceaccount","keyId":"k1","key":PRIVATE_PEM,"userId":"u1"}).to_string(),
    )
    .unwrap();
    std::fs::set_permissions(&key_file, std::fs::Permissions::from_mode(0o600)).unwrap();
    let cfg = BacklinksConfig {
        url: sidecar.url(),
        issuer: issuer.url(),
        key_file,
        audience_scopes: vec!["s".into()],
        timeout: Duration::from_millis(5000),
    };
    let w = bound(&fossil, move |c| c.backlinks = Some(cfg)).await;
    assert_code(
        call(&w, args("Target", None, None)).await,
        ErrorCode::BacklinksAuthFailed,
    );
    assert_eq!(sidecar.count(), 0);
}

// ---- credential handling -------------------------------------------------------

#[tokio::test]
async fn unusable_key_file_is_credential_unavailable_without_the_path() {
    let e = env(|_, _| Reply::json(200, page_body(json!([]))), 3600);
    let w = wiki(&e, 5000).await;
    std::fs::set_permissions(&e.key_file, std::fs::Permissions::from_mode(0o644)).unwrap();
    let err = assert_code(
        call(&w, args("Target", None, None)).await,
        ErrorCode::CredentialUnavailable,
    );
    assert!(!err.contains("SENTINEL"), "{err}");
    std::fs::remove_file(&e.key_file).unwrap();
    let err = assert_code(
        call(&w, args("Target", None, None)).await,
        ErrorCode::CredentialUnavailable,
    );
    assert!(!err.contains("SENTINEL"), "{err}");
    assert_eq!(e.sidecar.count(), 0);
}

#[tokio::test]
async fn token_and_key_never_appear_in_output() {
    let e = env(|_, _| Reply::json(200, page_body(rows(3))), 3600);
    let w = wiki(&e, 5000).await;
    let r = w.wiki_backlinks(args("Target", None, None)).await.unwrap();
    let wire = serde_json::to_string(&r.0).unwrap();
    for banned in ["tok1", "PRIVATE KEY", "SENTINEL", "Bearer"] {
        assert!(!wire.contains(banned), "{banned} in {wire}");
    }
}

// ---- gating -------------------------------------------------------------------

#[tokio::test]
async fn startup_rejects_invalid_backlinks_config() {
    let e = env(|_, _| Reply::json(200, page_body(json!([]))), 3600);
    let good = BacklinksConfig {
        url: "https://sidecar.example".into(),
        issuer: "https://issuer.example".into(),
        key_file: e.key_file.clone(),
        audience_scopes: vec!["s".into()],
        timeout: Duration::from_millis(10_000),
    };
    let mut bad: Vec<BacklinksConfig> = Vec::new();
    for url in [
        "http://sidecar.example",
        "https://sidecar.example/v1",
        "https://u@sidecar.example",
        "",
    ] {
        bad.push(BacklinksConfig {
            url: url.into(),
            ..good.clone()
        });
    }
    bad.push(BacklinksConfig {
        issuer: "http://issuer.example".into(),
        ..good.clone()
    });
    bad.push(BacklinksConfig {
        audience_scopes: vec![],
        ..good.clone()
    });
    bad.push(BacklinksConfig {
        audience_scopes: vec!["has space".into()],
        ..good.clone()
    });
    for t in [0u64, 999, 60_001] {
        bad.push(BacklinksConfig {
            timeout: Duration::from_millis(t),
            ..good.clone()
        });
    }
    for (i, cfg) in bad.into_iter().enumerate() {
        let mut wc = fossil_mcp::WikiConfig::new("repo1", e.fossil.repo_file());
        wc.fossil_bin = e.fossil.bin.clone();
        wc.backlinks = Some(cfg);
        let r = FossilWiki::bind(wc).await;
        assert!(
            matches!(r, Err(fossil_mcp::StartupError::InvalidBacklinksConfig)),
            "case {i}"
        );
    }
    let mut wc = fossil_mcp::WikiConfig::new("repo1", e.fossil.repo_file());
    wc.fossil_bin = e.fossil.bin.clone();
    wc.backlinks = Some(good);
    assert!(FossilWiki::bind(wc).await.is_ok(), "the good config binds");
}

#[tokio::test]
async fn tool_is_absent_without_configuration() {
    let f = FakeFossil::new();
    let w = bound(&f, |_| {}).await;
    use rmcp::handler::server::ServerHandler;
    assert!(w.get_tool("wiki_backlinks").is_none());
    let e = env(|_, _| Reply::json(200, page_body(json!([]))), 3600);
    let w = wiki(&e, 5000).await;
    let t = w
        .get_tool("wiki_backlinks")
        .expect("present when configured");
    let a = t.annotations.expect("annotations");
    assert_eq!(a.read_only_hint, Some(true));
    assert_eq!(a.destructive_hint, Some(false));
    assert_eq!(a.idempotent_hint, Some(true));
    assert_eq!(a.open_world_hint, Some(true));
}

// ---- properties ----------------------------------------------------------------

fn percent_decode(s: &str) -> String {
    let b = s.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < b.len() {
        if b[i] == b'%' {
            out.push(u8::from_str_radix(&s[i + 1..i + 3], 16).unwrap());
            i += 3;
        } else {
            out.push(b[i]);
            i += 1;
        }
    }
    String::from_utf8(out).unwrap()
}

proptest! {
    #[test]
    fn cursor_round_trips(generation in any::<u64>(), offset in any::<u64>()) {
        let c = Cursor { generation, offset };
        prop_assert_eq!(Cursor::parse(&c.to_string()), Some(c));
    }

    #[test]
    fn cursor_parse_never_panics_and_is_canonical(s in "\\PC{0,24}") {
        if let Some(c) = Cursor::parse(&s) {
            prop_assert_eq!(c.to_string(), s);
        }
    }

    #[test]
    fn page_names_survive_url_encoding(name in "[^\\x00\\r\\n-][^\\x00\\r\\n]{0,40}") {
        let enc = percent_encode(&name);
        prop_assert!(enc.bytes().all(|b| b.is_ascii_alphanumeric() || b"-._~%".contains(&b)));
        prop_assert_eq!(percent_decode(&enc), name);
    }
}

#[tokio::test]
async fn concurrent_calls_share_one_token_request() {
    let hits = Arc::new(AtomicUsize::new(0));
    let h = hits.clone();
    let e = env(
        move |_, _| {
            h.fetch_add(1, Ordering::SeqCst);
            Reply::json(200, page_body(json!([])))
        },
        3600,
    );
    let w = wiki(&e, 5000).await;
    let (a, b, c) = tokio::join!(
        call(&w, args("Target", None, None)),
        call(&w, args("Target", None, None)),
        call(&w, args("Target", None, None)),
    );
    a.unwrap();
    b.unwrap();
    c.unwrap();
    assert_eq!(hits.load(Ordering::SeqCst), 3);
    assert_eq!(e.issuer.count(), 1, "single flight");
}

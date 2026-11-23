//! I2: application-held copies of the assertion, the form body and token
//! response bodies are wiped on drop, and none of them can be printed.
//!
//! What is checkable here is the types: the buffers are `Zeroizing`, so wiping
//! on every exit (success, `?`, panic unwinding) is the type's `Drop`. Copies
//! made inside ureq (request/response buffers), rustls and serde_json cannot be
//! reached from this crate and are documented as residual exposure in
//! `server::secret`.
mod fake_http;

use fake_http::{Fake, Reply};
use fossil_mcp::server::backlinks::client::{HttpClient, HttpConfig, HttpResponse};
use fossil_mcp::server::backlinks::token::build_assertion;
use fossil_mcp::server::secret::{Secret, ZitadelKey};
use serde_json::json;
use std::time::Duration;
use zeroize::Zeroizing;

const PEM: &str = include_str!("fixtures/test-rsa-private.pem");

fn key() -> ZitadelKey {
    let doc = json!({"type":"serviceaccount","keyId":"k","userId":"u","key":PEM}).to_string();
    ZitadelKey::parse(&Secret::new(doc.into_bytes())).unwrap()
}

fn http(max_body: usize) -> HttpClient {
    HttpClient::new(HttpConfig {
        timeout: Duration::from_secs(5),
        connect_timeout: Duration::from_secs(2),
        max_body,
    })
}

#[test]
fn assertion_is_a_zeroizing_string() {
    let a: Zeroizing<String> = build_assertion(&key(), "https://issuer.example", 1_000).unwrap();
    assert_eq!(a.split('.').count(), 3);
}

#[test]
fn response_body_is_zeroizing_and_not_printed() {
    let fake = Fake::start(|_, _| Reply::json(200, json!({"access_token":"SENTINEL-TOKEN-BODY"})));
    let r: HttpResponse = http(4096).get(&fake.url(), None).unwrap();
    let body: &Zeroizing<Vec<u8>> = &r.body;
    assert!(String::from_utf8_lossy(body).contains("SENTINEL-TOKEN-BODY"));
    let dbg = format!("{r:?}");
    assert!(!dbg.contains("SENTINEL"), "{dbg}");
    assert!(!dbg.contains("115, 101"), "bytes printed: {dbg}");
    assert!(dbg.contains("200"), "{dbg}");
}

#[test]
fn bodies_larger_than_one_read_chunk_arrive_intact_and_capped() {
    let big = "x".repeat(100_000);
    let b = big.clone();
    let fake = Fake::start(move |_, _| Reply::json(200, json!({ "v": b })));
    let r = http(1 << 20).get(&fake.url(), None).unwrap();
    assert_eq!(r.body.len(), 100_000 + r#"{"v":""}"#.len());
    let too_small = http(50_000).get(&fake.url(), None);
    assert_eq!(
        too_small.unwrap_err(),
        fossil_mcp::server::backlinks::client::HttpError::TooLarge
    );
}

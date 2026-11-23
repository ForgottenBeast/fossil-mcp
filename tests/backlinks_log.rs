//! I1: dependency logs must never carry the bearer token or the assertion,
//! whatever logger the embedding application installs.
//!
//! `ureq-proto` logs raw request and response bytes at TRACE through the `log`
//! facade. This test installs a logger that accepts every level, performs a
//! full token exchange plus an authenticated GET against loopback fakes, and
//! checks the captured records (and the bytes reconstructed from the hex dump
//! rows) for the secrets. It is its own test binary because the `log` logger
//! is process-global.
mod fake_http;

use fake_http::{Fake, Reply};
use fossil_mcp::server::backlinks::Origin;
use fossil_mcp::server::backlinks::client::{HttpClient, HttpConfig};
use fossil_mcp::server::backlinks::token::TokenCache;
use fossil_mcp::server::secret::{Secret, SecretError, SecretSource};
use serde_json::json;
use std::sync::{Arc, Mutex};
use std::time::Duration;

const PEM: &str = include_str!("fixtures/test-rsa-private.pem");
const TOKEN: &str = "LOGTEST-ACCESS-TOKEN-0123456789abcdef";

struct Source;
impl SecretSource for Source {
    fn read(&self) -> Result<Secret, SecretError> {
        Ok(Secret::new(
            json!({"type":"serviceaccount","keyId":"k","userId":"u","key":PEM})
                .to_string()
                .into_bytes(),
        ))
    }
}

static RECORDS: Mutex<Vec<(String, log::Level, String)>> = Mutex::new(Vec::new());

struct Capture;
impl log::Log for Capture {
    fn enabled(&self, _: &log::Metadata) -> bool {
        true
    }
    fn log(&self, r: &log::Record) {
        RECORDS
            .lock()
            .unwrap()
            .push((r.target().to_string(), r.level(), r.args().to_string()));
    }
    fn flush(&self) {}
}
static CAPTURE: Capture = Capture;

fn http(cap: usize) -> HttpClient {
    HttpClient::new(HttpConfig {
        timeout: Duration::from_secs(5),
        connect_timeout: Duration::from_secs(2),
        max_body: cap,
    })
}

/// Bytes of every `xxxx xxxx ... ascii` hex-dump row, concatenated.
fn reconstruct_wire(lines: &[String]) -> String {
    let mut wire = Vec::new();
    for line in lines {
        let Some(head) = line.get(..40) else { continue };
        let hex: String = head.chars().filter(char::is_ascii_hexdigit).collect();
        if hex.len().is_multiple_of(2) {
            for i in (0..hex.len()).step_by(2) {
                if let Ok(b) = u8::from_str_radix(&hex[i..i + 2], 16) {
                    wire.push(b);
                }
            }
        }
    }
    String::from_utf8_lossy(&wire).into_owned()
}

#[test]
fn dependency_logs_never_contain_token_or_assertion() {
    log::set_logger(&CAPTURE).unwrap();
    log::set_max_level(log::LevelFilter::Trace);

    let issuer =
        Fake::start(|_, _| Reply::json(200, json!({"access_token":TOKEN,"expires_in":3600})));
    let cache = TokenCache::new(
        Arc::new(Source),
        Arc::new(http(65536)),
        Origin::parse(&issuer.url()).unwrap(),
        vec!["aud-scope".into()],
    );
    let token = cache.get().unwrap();
    let sidecar = Fake::start(|_, _| Reply::json(200, json!({"ok":true})));
    http(1024)
        .get(&sidecar.url(), Some(token.secret()))
        .unwrap();

    let body = issuer.requests()[0].body.clone();
    let assertion = String::from_utf8_lossy(&body)
        .split("assertion=")
        .nth(1)
        .unwrap()
        .to_owned();
    assert!(assertion.len() > 100);

    let records = RECORDS.lock().unwrap().clone();
    let lines: Vec<String> = records.iter().map(|(_, _, m)| m.clone()).collect();
    let wire = reconstruct_wire(&lines);
    let raw = lines.join("\n");
    for (name, haystack) in [("records", &raw), ("hex-dump wire", &wire)] {
        assert!(!haystack.contains(TOKEN), "token in {name}");
        assert!(
            !haystack.contains(&format!("Bearer {TOKEN}")),
            "bearer in {name}"
        );
        assert!(!haystack.contains(&assertion), "assertion in {name}");
        assert!(!haystack.contains("assertion="), "form body in {name}");
    }
    // Nothing below INFO may come out of the HTTP stack at all.
    let verbose: Vec<_> = records
        .iter()
        .filter(|(t, l, _)| {
            (t.starts_with("ureq") || t.starts_with("rustls")) && *l > log::Level::Info
        })
        .map(|(t, l, _)| format!("{l} {t}"))
        .collect();
    assert!(verbose.is_empty(), "verbose dependency logs: {verbose:?}");
}

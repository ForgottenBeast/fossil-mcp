//! I1: dependency logs must never carry the bearer token or the assertion,
//! whatever logger or subscriber the embedding application installs and
//! whatever `log` level features it compiles in.
//!
//! The HTTP stack (hyper without its unstable `tracing` feature, rustls
//! without its `logging` feature) has no logging call that can see request
//! bytes, so there is nothing for a downstream crate to switch back on. This
//! test proves it: it installs a `log` logger and a `tracing` subscriber that
//! accept every level, performs a full token exchange plus an authenticated
//! GET against loopback fakes, and checks every captured record from every
//! crate for the secrets, and that no HTTP-stack crate logs at all.
//!
//! A downstream consumer's release build is simulated by the dev-dependency
//! `log/release_max_level_trace`: run this file with
//! `cargo test --release --test backlinks_log` and the cap is lifted exactly
//! as an embedding application could lift it. (A debug build never applies
//! `release_max_level_*`, so both profiles are meaningful.) It is its own test
//! binary because both global subscribers are process-wide.
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

/// A `tracing` subscriber that enables everything and records events and span
/// names with every field rendered through `Debug`.
struct TraceCapture;
struct Fields(String);
impl tracing::field::Visit for Fields {
    fn record_debug(&mut self, f: &tracing::field::Field, v: &dyn std::fmt::Debug) {
        use std::fmt::Write;
        let _ = write!(self.0, "{}={:?} ", f.name(), v);
    }
}
impl tracing::Subscriber for TraceCapture {
    fn enabled(&self, _: &tracing::Metadata<'_>) -> bool {
        true
    }
    fn new_span(&self, a: &tracing::span::Attributes<'_>) -> tracing::span::Id {
        let mut f = Fields(a.metadata().name().to_string());
        a.record(&mut f);
        RECORDS
            .lock()
            .unwrap()
            .push((a.metadata().target().to_string(), log::Level::Trace, f.0));
        tracing::span::Id::from_u64(1)
    }
    fn record(&self, _: &tracing::span::Id, _: &tracing::span::Record<'_>) {}
    fn record_follows_from(&self, _: &tracing::span::Id, _: &tracing::span::Id) {}
    fn event(&self, e: &tracing::Event<'_>) {
        let mut f = Fields(String::new());
        e.record(&mut f);
        RECORDS
            .lock()
            .unwrap()
            .push((e.metadata().target().to_string(), log::Level::Trace, f.0));
    }
    fn enter(&self, _: &tracing::span::Id) {}
    fn exit(&self, _: &tracing::span::Id) {}
}

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
    tracing::subscriber::set_global_default(TraceCapture).unwrap();

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
    // No crate of the HTTP stack may log at all: only this crate's own
    // records (and this test's) are allowed to exist.
    let foreign: Vec<_> = records
        .iter()
        .filter(|(t, _, _)| !(t.starts_with("fossil_mcp") || t.starts_with("backlinks_log")))
        .map(|(t, l, _)| format!("{l} {t}"))
        .collect();
    assert!(foreign.is_empty(), "dependency log records: {foreign:?}");
}

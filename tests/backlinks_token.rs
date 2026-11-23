//! F1: opaque secrets, the Zitadel key file, the JWT-profile assertion, the
//! token cache and the bounded HTTP client, against a fake issuer on loopback.
mod fake_http;

use fake_http::{Fake, Reply, Req};
use fossil_mcp::server::backlinks::Origin;
use fossil_mcp::server::backlinks::client::{HttpClient, HttpConfig, HttpError};
use fossil_mcp::server::backlinks::token::{TokenCache, build_assertion};
use fossil_mcp::server::secret::{
    FileSecretSource, MAX_SECRET_BYTES, Secret, SecretError, SecretSource, ZitadelKey,
};
use fossil_mcp::server::types::ErrorCode;
use jsonwebtoken::{Algorithm, DecodingKey, Validation, decode, decode_header};
use serde_json::{Value, json};
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;

const PRIVATE_PEM: &str = include_str!("fixtures/test-rsa-private.pem");
const PUBLIC_PEM: &str = include_str!("fixtures/test-rsa-public.pem");
const SCOPE: &str = "urn:zitadel:iam:org:project:id:42:aud";

fn key_json() -> String {
    json!({"type":"serviceaccount","keyId":"key-1","key":PRIVATE_PEM,"userId":"user-7"}).to_string()
}

fn write_key(dir: &Path, content: &str, mode: u32) -> PathBuf {
    let p = dir.join("key.json");
    std::fs::write(&p, content).unwrap();
    std::fs::set_permissions(&p, std::fs::Permissions::from_mode(mode)).unwrap();
    p
}

fn http() -> Arc<HttpClient> {
    Arc::new(HttpClient::new(HttpConfig {
        timeout: Duration::from_secs(5),
        connect_timeout: Duration::from_secs(2),
        max_body: 64 * 1024,
    }))
}

// ---- Secret / FileSecretSource -------------------------------------------

#[test]
fn secret_debug_is_redacted() {
    let s = Secret::new(b"SENTINEL-KEY-BYTES".to_vec());
    let d = format!("{s:?}");
    assert_eq!(d, "Secret(<redacted>)");
    assert!(!d.contains("SENTINEL"));
}

#[test]
fn file_source_reads_valid_file_and_parses_key() {
    let dir = tempfile::tempdir().unwrap();
    for mode in [0o600, 0o640, 0o400] {
        let p = write_key(dir.path(), &key_json(), mode);
        let secret = FileSecretSource::new(&p).read().expect("valid file");
        let key = ZitadelKey::parse(&secret).expect("valid key json");
        assert_eq!(key.key_id(), "key-1");
        assert_eq!(key.user_id(), "user-7");
        let dbg = format!("{key:?}");
        assert!(!dbg.contains("PRIVATE KEY"), "{dbg}");
        assert!(!dbg.contains(PRIVATE_PEM.lines().nth(1).unwrap()), "{dbg}");
    }
}

#[test]
fn file_source_rejects_unsafe_files() {
    let dir = tempfile::tempdir().unwrap();
    let missing = dir.path().join("nope");
    assert!(FileSecretSource::new(&missing).read().is_err());

    for mode in [0o644, 0o604, 0o660, 0o666, 0o602] {
        let p = write_key(dir.path(), &key_json(), mode);
        assert_eq!(
            FileSecretSource::new(&p).read().unwrap_err(),
            SecretError::Unsafe,
            "mode {mode:o}"
        );
    }

    let real = write_key(dir.path(), &key_json(), 0o600);
    let link = dir.path().join("link.json");
    std::os::unix::fs::symlink(&real, &link).unwrap();
    assert_eq!(
        FileSecretSource::new(&link).read().unwrap_err(),
        SecretError::Unsafe,
        "symlink"
    );

    assert!(
        FileSecretSource::new(dir.path()).read().is_err(),
        "directory"
    );

    let big = write_key(
        dir.path(),
        &"x".repeat(MAX_SECRET_BYTES as usize + 1),
        0o600,
    );
    assert_eq!(
        FileSecretSource::new(&big).read().unwrap_err(),
        SecretError::Unsafe,
        "oversize"
    );
    let ok = write_key(dir.path(), &"x".repeat(MAX_SECRET_BYTES as usize), 0o600);
    assert!(FileSecretSource::new(&ok).read().is_ok(), "at the limit");
}

#[test]
fn errors_never_contain_the_path() {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("SENTINEL-PATH-key.json");
    let e = FileSecretSource::new(&p).read().unwrap_err();
    assert!(!e.to_string().contains("SENTINEL"));
    assert!(!format!("{e:?}").contains("SENTINEL"));
}

#[test]
fn zitadel_key_parse_rejects_malformed_documents() {
    for doc in [
        "not json".to_string(),
        json!({"type":"application","keyId":"k","key":PRIVATE_PEM,"userId":"u"}).to_string(),
        json!({"type":"serviceaccount","keyId":"","key":PRIVATE_PEM,"userId":"u"}).to_string(),
        json!({"type":"serviceaccount","keyId":"k","key":PRIVATE_PEM,"userId":""}).to_string(),
        json!({"type":"serviceaccount","keyId":"k","key":"","userId":"u"}).to_string(),
        json!({"type":"serviceaccount","keyId":"k","userId":"u"}).to_string(),
    ] {
        let r = ZitadelKey::parse(&Secret::new(doc.into_bytes()));
        assert_eq!(r.unwrap_err(), SecretError::Invalid);
    }
}

// ---- assertion -------------------------------------------------------------

#[test]
fn assertion_has_kid_and_profile_claims_and_verifies_with_the_public_half() {
    let key = ZitadelKey::parse(&Secret::new(key_json().into_bytes())).unwrap();
    let issuer = "https://issuer.example";
    let now = 1_700_000_000;
    let jwt = build_assertion(&key, issuer, now).unwrap();

    let header = decode_header(&jwt).unwrap();
    assert_eq!(header.alg, Algorithm::RS256);
    assert_eq!(header.kid.as_deref(), Some("key-1"));

    let mut v = Validation::new(Algorithm::RS256);
    v.set_audience(&[issuer]);
    v.set_issuer(&["user-7"]);
    v.validate_exp = false; // fixed clock above; exp is asserted explicitly
    v.set_required_spec_claims(&["aud", "iss", "sub"]);
    let data = decode::<Value>(
        &jwt,
        &DecodingKey::from_rsa_pem(PUBLIC_PEM.as_bytes()).unwrap(),
        &v,
    )
    .expect("verifies with the public key");
    let c = data.claims;
    assert_eq!(c["iss"], "user-7");
    assert_eq!(c["sub"], "user-7");
    assert_eq!(c["aud"], issuer);
    assert_eq!(c["iat"], now);
    assert_eq!(c["exp"].as_u64().unwrap() - c["iat"].as_u64().unwrap(), 300);
}

#[test]
fn assertion_with_unusable_key_is_credential_unavailable() {
    let doc = json!({"type":"serviceaccount","keyId":"k","key":"not a pem","userId":"u"});
    let key = ZitadelKey::parse(&Secret::new(doc.to_string().into_bytes())).unwrap();
    assert_eq!(
        build_assertion(&key, "https://i.example", 1).unwrap_err(),
        ErrorCode::CredentialUnavailable
    );
}

// ---- origin ----------------------------------------------------------------

#[test]
fn origin_accepts_https_and_loopback_http_only() {
    assert_eq!(
        Origin::parse("https://a.example").unwrap().as_str(),
        "https://a.example"
    );
    assert_eq!(
        Origin::parse("https://a.example/").unwrap().as_str(),
        "https://a.example"
    );
    assert!(Origin::parse("https://a.example:8443").is_ok());
    assert!(Origin::parse("http://127.0.0.1:8080").is_ok());
    assert!(Origin::parse("http://[::1]:8080").is_ok());
    for bad in [
        "http://a.example",
        "http://localhost:8080",
        "http://127.0.0.1.example",
        "ftp://a.example",
        "https://a.example/path",
        "https://a.example/?q=1",
        "https://a.example?q=1",
        "https://user@a.example",
        "https://user:pw@a.example",
        "https://a.example/#frag",
        "a.example",
        "",
        "https://",
    ] {
        assert!(Origin::parse(bad).is_err(), "{bad:?} must be rejected");
    }
}

// ---- token cache against a fake issuer -----------------------------------------

fn issuer_ok(expires_in: u64) -> impl Fn(&Req, usize) -> Reply + Send + Sync + 'static {
    move |req, idx| {
        assert_eq!(req.method, "POST");
        assert_eq!(req.target, "/oauth/v2/token");
        assert_eq!(
            req.header("content-type"),
            Some("application/x-www-form-urlencoded")
        );
        Reply::json(
            200,
            json!({"access_token": format!("tok{}", idx + 1), "expires_in": expires_in,
                   "token_type": "Bearer"}),
        )
    }
}

fn cache(fake: &Fake, dir: &Path) -> TokenCache {
    let p = write_key(dir, &key_json(), 0o600);
    TokenCache::new(
        Arc::new(FileSecretSource::new(p)),
        http(),
        Origin::parse(&fake.url()).unwrap(),
        vec![SCOPE.to_string()],
    )
}

fn form(body: &[u8]) -> Vec<(String, String)> {
    String::from_utf8(body.to_vec())
        .unwrap()
        .split('&')
        .map(|kv| {
            let (k, v) = kv.split_once('=').unwrap();
            (dec(k), dec(v))
        })
        .collect()
}

fn dec(s: &str) -> String {
    let b = s.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'+' => out.push(b' '),
            b'%' => {
                out.push(u8::from_str_radix(&s[i + 1..i + 3], 16).unwrap());
                i += 2;
            }
            c => out.push(c),
        }
        i += 1;
    }
    String::from_utf8(out).unwrap()
}

#[test]
fn token_request_is_a_jwt_profile_grant_with_scopes() {
    let fake = Fake::start(issuer_ok(3600));
    let dir = tempfile::tempdir().unwrap();
    let c = cache(&fake, dir.path());
    let t = c.get().unwrap();
    assert_eq!(t.secret().expose(), b"tok1");
    let reqs = fake.requests();
    assert_eq!(reqs.len(), 1);
    let f = form(&reqs[0].body);
    let get = |k: &str| f.iter().find(|(n, _)| n == k).map(|(_, v)| v.as_str());
    assert_eq!(
        get("grant_type"),
        Some("urn:ietf:params:oauth:grant-type:jwt-bearer")
    );
    assert_eq!(get("scope"), Some(format!("openid {SCOPE}").as_str()));
    let assertion = get("assertion").unwrap();
    let mut v = Validation::new(Algorithm::RS256);
    v.set_audience(&[fake.url().as_str()]);
    v.set_issuer(&["user-7"]);
    decode::<Value>(
        assertion,
        &DecodingKey::from_rsa_pem(PUBLIC_PEM.as_bytes()).unwrap(),
        &v,
    )
    .expect("assertion verifies, aud is the issuer");
}

#[test]
fn cached_token_is_reused() {
    let fake = Fake::start(issuer_ok(3600));
    let dir = tempfile::tempdir().unwrap();
    let c = cache(&fake, dir.path());
    let a = c.get().unwrap();
    let b = c.get().unwrap();
    assert_eq!(a.secret().expose(), b.secret().expose());
    assert_eq!(fake.count(), 1, "two gets, one token request");
}

#[test]
fn token_not_outliving_the_refresh_margin_is_an_auth_failure() {
    // A token that would already be inside the 60 s refresh margin can never
    // be served from the cache; the issuer is misconfigured, so it is an
    // operator-visible auth failure, not a token handed out uncached.
    for expires_in in [0, 1, 59, 60] {
        let fake = Fake::start(issuer_ok(expires_in));
        let dir = tempfile::tempdir().unwrap();
        let c = cache(&fake, dir.path());
        assert_eq!(
            c.get().unwrap_err(),
            ErrorCode::BacklinksAuthFailed,
            "expires_in {expires_in}"
        );
        assert_eq!(fake.count(), 1);
    }
}

#[test]
fn token_just_past_the_refresh_margin_is_cached() {
    let fake = Fake::start(issuer_ok(61));
    let dir = tempfile::tempdir().unwrap();
    let c = cache(&fake, dir.path());
    c.get().unwrap();
    c.get().unwrap();
    assert_eq!(fake.count(), 1);
}

#[test]
fn expires_in_is_capped_at_twelve_hours() {
    // A huge expires_in must not overflow or extend past the cap; the token
    // is still cached and reused.
    let fake = Fake::start(issuer_ok(u64::MAX / 4));
    let dir = tempfile::tempdir().unwrap();
    let c = cache(&fake, dir.path());
    c.get().unwrap();
    c.get().unwrap();
    assert_eq!(fake.count(), 1);
}

#[test]
fn rejected_token_is_replaced_once_and_only_if_still_current() {
    let fake = Fake::start(issuer_ok(3600));
    let dir = tempfile::tempdir().unwrap();
    let c = cache(&fake, dir.path());
    let first = c.get().unwrap();
    let second = c.refresh_rejected(&first).unwrap();
    assert_eq!(second.secret().expose(), b"tok2");
    // A late report about the already replaced token does not refresh again.
    let again = c.refresh_rejected(&first).unwrap();
    assert_eq!(again.secret().expose(), b"tok2");
    assert_eq!(fake.count(), 2);
}

#[test]
fn rotated_key_file_is_picked_up_on_refresh() {
    let fake = Fake::start(issuer_ok(3600));
    let dir = tempfile::tempdir().unwrap();
    let c = cache(&fake, dir.path());
    let first = c.get().unwrap();
    // Rotation: the file now holds an unusable key; the next refresh sees it.
    let bad = json!({"type":"serviceaccount","keyId":"k","key":"nope","userId":"u"});
    write_key(dir.path(), &bad.to_string(), 0o600);
    assert_eq!(
        c.refresh_rejected(&first).unwrap_err(),
        ErrorCode::CredentialUnavailable
    );
    assert_eq!(fake.count(), 1, "no request without a usable key");
}

#[test]
fn issuer_client_error_is_auth_failed() {
    let fake = Fake::start(|_, _| Reply::json(400, json!({"error":"invalid_grant"})));
    let dir = tempfile::tempdir().unwrap();
    let c = cache(&fake, dir.path());
    assert_eq!(c.get().unwrap_err(), ErrorCode::BacklinksAuthFailed);
    assert_eq!(fake.count(), 1, "no retry of a rejected grant");
}

#[test]
fn issuer_server_error_is_unreachable() {
    let fake = Fake::start(|_, _| Reply::json(503, json!({})));
    let dir = tempfile::tempdir().unwrap();
    let c = cache(&fake, dir.path());
    assert_eq!(c.get().unwrap_err(), ErrorCode::BacklinksUnreachable);
}

#[test]
fn malformed_token_responses_are_bad_response() {
    for body in [
        json!({"expires_in": 3600}),
        json!({"access_token": "", "expires_in": 3600}),
        json!({"access_token": "has space", "expires_in": 3600}),
        json!({"access_token": "line\nbreak", "expires_in": 3600}),
        json!({"access_token": "x".repeat(9000), "expires_in": 3600}),
        json!({"access_token": "tok"}),
        json!("not an object"),
    ] {
        let fake = Fake::start(move |_, _| Reply::json(200, body.clone()));
        let dir = tempfile::tempdir().unwrap();
        let c = cache(&fake, dir.path());
        assert_eq!(c.get().unwrap_err(), ErrorCode::BadResponse);
    }
}

#[test]
fn token_never_appears_in_errors_or_debug() {
    let fake = Fake::start(issuer_ok(3600));
    let dir = tempfile::tempdir().unwrap();
    let c = cache(&fake, dir.path());
    let t = c.get().unwrap();
    assert!(!format!("{t:?}").contains("tok1"));
    assert!(!format!("{c:?}").contains("tok1"));
}

// ---- bounded client ----------------------------------------------------------

fn client_with(timeout_ms: u64, max_body: usize) -> HttpClient {
    HttpClient::new(HttpConfig {
        timeout: Duration::from_millis(timeout_ms),
        connect_timeout: Duration::from_millis(timeout_ms),
        max_body,
    })
}

#[test]
fn client_sends_bearer_and_accept_and_returns_status_and_body() {
    let fake = Fake::start(|_, _| Reply::json(200, json!({"a": 1})));
    let c = client_with(5000, 1024);
    let s = Secret::new(b"tok-abc".to_vec());
    let r = c.get(&format!("{}/x?y=1", fake.url()), Some(&s)).unwrap();
    assert_eq!(r.status, 200);
    assert_eq!(&r.body[..], br#"{"a":1}"#);
    let req = &fake.requests()[0];
    assert_eq!(req.target, "/x?y=1");
    assert_eq!(req.header("authorization"), Some("Bearer tok-abc"));
    assert_eq!(req.header("accept"), Some("application/json"));
}

#[test]
fn client_returns_error_statuses_without_following_redirects() {
    let fake = Fake::start(|_, _| Reply::Full {
        status: 302,
        body: b"{}".to_vec(),
    });
    let c = client_with(5000, 1024);
    let r = c.get(&format!("{}/x", fake.url()), None).unwrap();
    assert_eq!(r.status, 302);
    assert_eq!(fake.count(), 1);
    let fake = Fake::start(|_, _| Reply::json(404, json!({})));
    assert_eq!(
        c.get(&format!("{}/x", fake.url()), None).unwrap().status,
        404
    );
}

#[test]
fn client_caps_the_response_body() {
    let fake = Fake::start(|_, _| Reply::Full {
        status: 200,
        body: vec![b'a'; 2048],
    });
    let c = client_with(5000, 1024);
    assert_eq!(
        c.get(&format!("{}/x", fake.url()), None).unwrap_err(),
        HttpError::TooLarge
    );
}

#[test]
fn client_deadline_covers_a_stalled_body() {
    let fake = Fake::start(|_, _| Reply::Stall {
        status: 200,
        stall: Duration::from_secs(4),
    });
    let c = client_with(1000, 1024 * 1024);
    let t = std::time::Instant::now();
    assert_eq!(
        c.get(&format!("{}/x", fake.url()), None).unwrap_err(),
        HttpError::Timeout
    );
    assert!(t.elapsed() < Duration::from_secs(3), "{:?}", t.elapsed());
}

#[test]
fn client_connect_failure_is_unreachable() {
    let port = {
        let l = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
        l.local_addr().unwrap().port()
    };
    let c = client_with(2000, 1024);
    assert_eq!(
        c.get(&format!("http://127.0.0.1:{port}/x"), None)
            .unwrap_err(),
        HttpError::Unreachable
    );
}

//! I2: secrets this crate decodes or parses are wiped before their memory is
//! returned to the allocator, on success and on every error path.
//!
//! The checks use a global allocator that inspects each block as it is freed:
//! a freed block that still holds the secret's bytes is an unwiped copy.
//! It is its own test binary because the allocator is process-global; the
//! cases run one at a time under a lock.
mod fake_http;

use fossil_mcp::server::backlinks::Origin;
use fossil_mcp::server::backlinks::client::{HttpClient, HttpConfig};
use fossil_mcp::server::backlinks::token::{TokenCache, build_assertion, check_signing_key};
use fossil_mcp::server::secret::{Secret, SecretError, SecretSource, ZitadelKey};
use rustls_pki_types::{PrivateKeyDer, pem::PemObject};
use serde_json::json;
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

const PEM: &str = include_str!("fixtures/test-rsa-private.pem");
const TOKEN: &[u8] = b"REVIEW10-TOKEN-SENTINEL-0123456789abcdef";

/// Bytes to look for in freed blocks. `Needle::len == 0` means disarmed.
struct Needle {
    ptr: AtomicPtr<u8>,
    len: AtomicUsize,
    /// `true`: a block must have exactly this size; `false`: at least.
    exact: AtomicUsize,
    hits: AtomicUsize,
}

static NEEDLE: Needle = Needle {
    ptr: AtomicPtr::new(std::ptr::null_mut()),
    len: AtomicUsize::new(0),
    exact: AtomicUsize::new(0),
    hits: AtomicUsize::new(0),
};

struct Probe;

unsafe impl GlobalAlloc for Probe {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        unsafe { System.alloc(l) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        let n = NEEDLE.len.load(Ordering::SeqCst);
        if n != 0 && l.size() >= n && (NEEDLE.exact.load(Ordering::SeqCst) == 0 || l.size() == n) {
            let want = unsafe { std::slice::from_raw_parts(NEEDLE.ptr.load(Ordering::SeqCst), n) };
            let have = unsafe { std::slice::from_raw_parts(p, n) };
            if want == have {
                NEEDLE.hits.fetch_add(1, Ordering::SeqCst);
            }
        }
        unsafe { System.dealloc(p, l) }
    }
}

#[global_allocator]
static ALLOC: Probe = Probe;

static SERIAL: Mutex<()> = Mutex::new(());

/// Count freed blocks holding `needle` while `f` runs. `needle` must outlive
/// the call and must not itself be freed inside `f`.
fn unwiped_copies(needle: &[u8], exact: bool, f: impl FnOnce()) -> usize {
    NEEDLE.hits.store(0, Ordering::SeqCst);
    NEEDLE.exact.store(usize::from(exact), Ordering::SeqCst);
    NEEDLE
        .ptr
        .store(needle.as_ptr() as *mut u8, Ordering::SeqCst);
    NEEDLE.len.store(needle.len(), Ordering::SeqCst);
    f();
    NEEDLE.len.store(0, Ordering::SeqCst);
    NEEDLE.hits.load(Ordering::SeqCst)
}

struct Source;
impl SecretSource for Source {
    fn read(&self) -> Result<Secret, SecretError> {
        Ok(Secret::new(key_doc().into_bytes()))
    }
}

fn key_doc() -> String {
    json!({"type":"serviceaccount","keyId":"k","userId":"u","key":PEM}).to_string()
}

fn zitadel_key() -> ZitadelKey {
    ZitadelKey::parse(&Secret::new(key_doc().into_bytes())).unwrap()
}

/// P2a: the token must not outlive a failed response parse. A malformed
/// `expires_in` after `access_token` used to abandon the decoded token.
#[test]
fn access_token_is_wiped_whether_or_not_the_response_parses() {
    let _guard = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    for (expires, parses) in [("3600", true), ("\"wrong-type\"", false)] {
        let body = format!(
            "{{\"access_token\":\"{}\",\"expires_in\":{expires}}}",
            std::str::from_utf8(TOKEN).unwrap()
        );
        let fake = fake_http::Fake::start(move |_, _| fake_http::Reply::Full {
            status: 200,
            body: body.clone().into_bytes(),
        });
        let cache = TokenCache::new(
            Arc::new(Source),
            Arc::new(HttpClient::new(HttpConfig {
                timeout: Duration::from_secs(5),
                connect_timeout: Duration::from_secs(2),
                max_body: 65536,
            })),
            Origin::parse(&fake.url()).unwrap(),
            vec!["scope".into()],
        );
        let mut ok = false;
        let count = unwiped_copies(TOKEN, true, || {
            let r = cache.get();
            ok = r.is_ok();
            drop(r);
            drop(cache);
        });
        assert_eq!(ok, parses, "expires_in={expires}");
        assert_eq!(count, 0, "unwiped token copies, expires_in={expires}");
    }
}

/// P2b: the decoded private-key DER must be wiped after signing, after the
/// startup validation, and when the key is rejected.
#[test]
fn private_key_der_is_wiped_on_every_exit() {
    let _guard = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    let reference: Vec<u8> = match PrivateKeyDer::from_pem_slice(PEM.as_bytes()).unwrap() {
        PrivateKeyDer::Pkcs1(k) => k.secret_pkcs1_der().to_vec(),
        PrivateKeyDer::Pkcs8(k) => k.secret_pkcs8_der().to_vec(),
        _ => panic!("unexpected fixture key kind"),
    };
    let key = zitadel_key();

    let signed = unwiped_copies(&reference, false, || {
        build_assertion(&key, "https://issuer.example", 1_000).unwrap();
    });
    assert_eq!(signed, 0, "unwiped DER copies after signing");

    let checked = unwiped_copies(&reference, false, || {
        check_signing_key(&key).unwrap();
    });
    assert_eq!(checked, 0, "unwiped DER copies after the startup check");

    // A valid PEM envelope around DER that ring rejects: the error exit.
    let mut bad = reference.clone();
    let last = bad.len() - 1;
    bad[last] ^= 0xff;
    bad.truncate(bad.len() - 8);
    let bad_pem = format!(
        "-----BEGIN RSA PRIVATE KEY-----\n{}\n-----END RSA PRIVATE KEY-----\n",
        b64(&bad)
    );
    let bad_key = ZitadelKey::parse(&Secret::new(
        json!({"type":"serviceaccount","keyId":"k","userId":"u","key":bad_pem})
            .to_string()
            .into_bytes(),
    ))
    .unwrap();
    let rejected = unwiped_copies(&bad, false, || {
        assert!(check_signing_key(&bad_key).is_err());
    });
    assert_eq!(rejected, 0, "unwiped DER copies on the error exit");
}

fn b64(data: &[u8]) -> String {
    const A: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::new();
    for c in data.chunks(3) {
        let n = c.iter().fold(0u32, |a, b| (a << 8) | u32::from(*b)) << (8 * (3 - c.len()));
        for i in 0..4 {
            if i <= c.len() {
                out.push(A[((n >> (18 - 6 * i)) & 63) as usize] as char);
            } else {
                out.push('=');
            }
        }
    }
    out
}

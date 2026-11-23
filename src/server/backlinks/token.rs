//! Zitadel JWT-profile token flow with an in-memory cache.
//!
//! The harness authenticates as a machine user: it signs a short-lived
//! assertion with the user's RSA key (read from a [`SecretSource`] on every
//! refresh, so rotation needs no restart) and exchanges it at
//! `<issuer>/oauth/v2/token` for an access token. The private key never
//! leaves the host and the token never appears in logs, errors or tool
//! output: every failure is a fixed [`ErrorCode`].

use super::Origin;
use super::client::{HttpClient, HttpError};
use crate::server::secret::{Secret, SecretSource, ZitadelKey};
use crate::server::types::ErrorCode;
use ring::rand::SystemRandom;
use ring::signature::{RSA_PKCS1_SHA256, RsaKeyPair};
use rustls_pki_types::PrivateKeyDer;
use rustls_pki_types::pem::PemObject;
use serde::{Deserialize, Serialize};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use zeroize::{Zeroize, Zeroizing};

/// A cached token is reused while more than this remains of its lifetime.
const REFRESH_MARGIN: Duration = Duration::from_secs(60);
/// Longest lifetime trusted from the issuer's `expires_in`.
const MAX_LIFETIME: Duration = Duration::from_secs(12 * 3600);
/// Lifetime of the signed assertion.
const ASSERTION_LIFETIME_SECS: u64 = 300;
/// Largest accepted access token in bytes.
const MAX_TOKEN_BYTES: usize = 8 * 1024;

/// An access token with the generation it was issued under.
#[derive(Clone)]
pub struct Token {
    secret: Secret,
    generation: u64,
}

impl Token {
    /// The bearer value. Callers must not log or format it.
    pub fn secret(&self) -> &Secret {
        &self.secret
    }
}

impl std::fmt::Debug for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Token")
            .field("secret", &self.secret)
            .field("generation", &self.generation)
            .finish()
    }
}

struct Cached {
    token: Token,
    expires: Instant,
}

#[derive(Default)]
struct State {
    cached: Option<Cached>,
    issued: u64,
}

/// Token cache for one machine user at one issuer.
///
/// One refresh is in flight at a time: the state lock is held across the
/// blocking exchange, so concurrent callers wait and then share the result.
pub struct TokenCache {
    source: Arc<dyn SecretSource>,
    http: Arc<HttpClient>,
    issuer: Origin,
    scope: String,
    state: Mutex<State>,
}

impl std::fmt::Debug for TokenCache {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TokenCache")
            .field("issuer", &self.issuer)
            .field("scope", &self.scope)
            .finish_non_exhaustive()
    }
}

#[derive(Serialize)]
struct AssertionHeader<'a> {
    alg: &'static str,
    typ: &'static str,
    kid: &'a str,
}

#[derive(Serialize)]
struct AssertionClaims<'a> {
    iss: &'a str,
    sub: &'a str,
    aud: &'a str,
    iat: u64,
    exp: u64,
}

/// Append `data` as unpadded base64url (RFC 4648 section 5).
fn push_b64url(out: &mut String, data: &[u8]) {
    const ALPHABET: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";
    for chunk in data.chunks(3) {
        let n = chunk.iter().fold(0u32, |a, b| (a << 8) | u32::from(*b)) << (8 * (3 - chunk.len()));
        for i in 0..=chunk.len() {
            out.push(ALPHABET[((n >> (18 - 6 * i)) & 63) as usize] as char);
        }
    }
}

/// Length of `n` bytes as unpadded base64url.
fn b64url_len(n: usize) -> usize {
    (n * 4).div_ceil(3)
}

/// Load the RSA signing key from a PEM document: PKCS#1 (`RSA PRIVATE KEY`,
/// what Zitadel issues) or PKCS#8 (`PRIVATE KEY`). ring rejects keys under
/// 2048 bits. The intermediate DER lives in a rustls-pki-types key that
/// wipes itself on drop; ring keeps the parsed key and has no wipe hook.
fn signing_key(pem: &[u8]) -> Result<RsaKeyPair, ErrorCode> {
    let der = PrivateKeyDer::from_pem_slice(pem).map_err(|_| ErrorCode::CredentialUnavailable)?;
    match &der {
        PrivateKeyDer::Pkcs1(k) => RsaKeyPair::from_der(k.secret_pkcs1_der()),
        PrivateKeyDer::Pkcs8(k) => RsaKeyPair::from_pkcs8(k.secret_pkcs8_der()),
        _ => return Err(ErrorCode::CredentialUnavailable),
    }
    .map_err(|_| ErrorCode::CredentialUnavailable)
}

/// Sign the JWT-profile assertion `{iss: userId, sub: userId, aud: issuer,
/// iat, exp: iat + 300}` with header `{alg: RS256, typ: JWT, kid: keyId}`.
///
/// RS256 is RSASSA-PKCS1-v1_5 over SHA-256 from ring (the `rsa` crate, with
/// its unfixed RUSTSEC-2023-0071 timing leak, is not used). The compact JWS is
/// assembled by hand in one pre-sized buffer that is wiped on drop; buffers
/// inside ring and rustls-pki-types are not reachable from here.
pub fn build_assertion(
    key: &ZitadelKey,
    issuer: &str,
    now_unix: u64,
) -> Result<Zeroizing<String>, ErrorCode> {
    let signer = signing_key(key.private_key_pem().expose())?;
    let header = serde_json::to_vec(&AssertionHeader {
        alg: "RS256",
        typ: "JWT",
        kid: key.key_id(),
    })
    .map_err(|_| ErrorCode::CredentialUnavailable)?;
    let claims = serde_json::to_vec(&AssertionClaims {
        iss: key.user_id(),
        sub: key.user_id(),
        aud: issuer,
        iat: now_unix,
        exp: now_unix + ASSERTION_LIFETIME_SECS,
    })
    .map_err(|_| ErrorCode::CredentialUnavailable)?;
    let sig_len = signer.public().modulus_len();
    let mut jws = Zeroizing::new(String::with_capacity(
        b64url_len(header.len()) + b64url_len(claims.len()) + b64url_len(sig_len) + 2,
    ));
    push_b64url(&mut jws, &header);
    jws.push('.');
    push_b64url(&mut jws, &claims);
    let mut sig = vec![0u8; sig_len];
    signer
        .sign(
            &RSA_PKCS1_SHA256,
            &SystemRandom::new(),
            jws.as_bytes(),
            &mut sig,
        )
        .map_err(|_| ErrorCode::CredentialUnavailable)?;
    jws.push('.');
    push_b64url(&mut jws, &sig);
    Ok(jws)
}

/// Whether the key's PEM is a usable RSA signing key (startup check; nothing
/// is signed or sent).
pub fn check_signing_key(key: &ZitadelKey) -> Result<(), ErrorCode> {
    signing_key(key.private_key_pem().expose()).map(|_| ())
}

/// The token endpoint's answer. `access_token` is wiped on drop, so every
/// early return leaves nothing behind (serde_json's own scratch is not
/// reachable).
#[derive(Deserialize)]
struct TokenResponse {
    access_token: Option<String>,
    expires_in: Option<u64>,
}

impl Drop for TokenResponse {
    fn drop(&mut self) {
        self.access_token.zeroize();
    }
}

impl TokenCache {
    /// A cache requesting `openid` plus `audience_scopes`.
    pub fn new(
        source: Arc<dyn SecretSource>,
        http: Arc<HttpClient>,
        issuer: Origin,
        audience_scopes: Vec<String>,
    ) -> Self {
        let mut scope = String::from("openid");
        for s in audience_scopes.iter().filter(|s| s.as_str() != "openid") {
            scope.push(' ');
            scope.push_str(s);
        }
        Self {
            source,
            http,
            issuer,
            scope,
            state: Mutex::new(State::default()),
        }
    }

    /// The cached token while it has more than 60 s left, else a fresh one.
    pub fn get(&self) -> Result<Token, ErrorCode> {
        let mut st = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        if let Some(t) = Self::fresh(&st) {
            return Ok(t);
        }
        self.refresh(&mut st)
    }

    /// The sidecar rejected `rejected`: fetch a replacement, unless another
    /// caller already replaced it (then that one is returned).
    pub fn refresh_rejected(&self, rejected: &Token) -> Result<Token, ErrorCode> {
        let mut st = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        if let Some(t) = Self::fresh(&st)
            && t.generation != rejected.generation
        {
            return Ok(t);
        }
        st.cached = None;
        self.refresh(&mut st)
    }

    fn fresh(st: &State) -> Option<Token> {
        st.cached
            .as_ref()
            .filter(|c| c.expires > Instant::now() + REFRESH_MARGIN)
            .map(|c| c.token.clone())
    }

    fn refresh(&self, st: &mut State) -> Result<Token, ErrorCode> {
        let raw = self
            .source
            .read()
            .map_err(|_| ErrorCode::CredentialUnavailable)?;
        let key = ZitadelKey::parse(&raw).map_err(|_| ErrorCode::CredentialUnavailable)?;
        drop(raw);
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|_| ErrorCode::CredentialUnavailable)?
            .as_secs();
        let assertion = build_assertion(&key, self.issuer.as_str(), now)?;
        drop(key);

        let started = Instant::now();
        let resp = self
            .http
            .post_form(
                &self.issuer.join("/oauth/v2/token"),
                &[
                    ("grant_type", "urn:ietf:params:oauth:grant-type:jwt-bearer"),
                    ("scope", &self.scope),
                    ("assertion", assertion.as_str()),
                ],
            )
            .map_err(|e| match e {
                HttpError::Timeout => ErrorCode::Timeout,
                HttpError::Unreachable => ErrorCode::BacklinksUnreachable,
                HttpError::TooLarge | HttpError::Protocol => ErrorCode::BadResponse,
            })?;
        tracing::debug!(
            status = resp.status,
            elapsed_ms = started.elapsed().as_millis() as u64,
            "token endpoint answered"
        );
        match resp.status {
            200 => {}
            400..=499 => return Err(ErrorCode::BacklinksAuthFailed),
            500..=599 => return Err(ErrorCode::BacklinksUnreachable),
            _ => return Err(ErrorCode::BadResponse),
        }
        let mut parsed: TokenResponse =
            serde_json::from_slice(&resp.body).map_err(|_| ErrorCode::BadResponse)?;
        // Check `expires_in` before taking the token out, so a rejection
        // leaves the token inside `parsed`, whose Drop wipes it.
        let Some(expires_in) = parsed.expires_in else {
            return Err(ErrorCode::BadResponse);
        };
        let Some(mut token) = parsed.access_token.take() else {
            return Err(ErrorCode::BadResponse);
        };
        if token.is_empty()
            || token.len() > MAX_TOKEN_BYTES
            || !token.bytes().all(|b| (0x21..=0x7e).contains(&b))
        {
            token.zeroize();
            return Err(ErrorCode::BadResponse);
        }
        // A lifetime inside the refresh margin could never be served from the
        // cache: the issuer's clock or token policy is wrong, so say so.
        if Duration::from_secs(expires_in) <= REFRESH_MARGIN {
            token.zeroize();
            return Err(ErrorCode::BacklinksAuthFailed);
        }
        st.issued += 1;
        let issued = Token {
            secret: Secret::new(token.into_bytes()),
            generation: st.issued,
        };
        st.cached = Some(Cached {
            token: issued.clone(),
            expires: Instant::now() + Duration::from_secs(expires_in).min(MAX_LIFETIME),
        });
        Ok(issued)
    }
}

#[cfg(test)]
mod tests {
    use super::{b64url_len, push_b64url};

    fn enc(data: &[u8]) -> String {
        let mut s = String::new();
        push_b64url(&mut s, data);
        s
    }

    #[test]
    fn base64url_matches_rfc4648_vectors() {
        for (input, want) in [
            ("", ""),
            ("f", "Zg"),
            ("fo", "Zm8"),
            ("foo", "Zm9v"),
            ("foob", "Zm9vYg"),
            ("fooba", "Zm9vYmE"),
            ("foobar", "Zm9vYmFy"),
        ] {
            assert_eq!(enc(input.as_bytes()), want, "{input:?}");
        }
    }

    #[test]
    fn base64url_uses_the_url_safe_alphabet_without_padding() {
        assert_eq!(enc(&[0xfb, 0xff, 0xbf]), "-_-_");
        assert_eq!(enc(&[0xfb, 0xff]), "-_8");
        assert!(!enc(&[0xff; 17]).contains(['=', '+', '/']));
    }

    #[test]
    fn base64url_len_is_exact() {
        for n in 0..64 {
            assert_eq!(enc(&vec![0xa5; n]).len(), b64url_len(n), "{n}");
        }
    }
}

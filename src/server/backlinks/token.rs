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
use jsonwebtoken::{Algorithm, EncodingKey, Header};
use serde::{Deserialize, Serialize};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use zeroize::Zeroize;

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
struct AssertionClaims<'a> {
    iss: &'a str,
    sub: &'a str,
    aud: &'a str,
    iat: u64,
    exp: u64,
}

/// Sign the JWT-profile assertion `{iss: userId, sub: userId, aud: issuer,
/// iat, exp: iat + 300}` with header `{alg: RS256, kid: keyId}`.
pub fn build_assertion(key: &ZitadelKey, issuer: &str, now_unix: u64) -> Result<String, ErrorCode> {
    let mut header = Header::new(Algorithm::RS256);
    header.kid = Some(key.key_id().to_string());
    let claims = AssertionClaims {
        iss: key.user_id(),
        sub: key.user_id(),
        aud: issuer,
        iat: now_unix,
        exp: now_unix + ASSERTION_LIFETIME_SECS,
    };
    let signing_key = EncodingKey::from_rsa_pem(key.private_key_pem().expose())
        .map_err(|_| ErrorCode::CredentialUnavailable)?;
    jsonwebtoken::encode(&header, &claims, &signing_key)
        .map_err(|_| ErrorCode::CredentialUnavailable)
}

#[derive(Deserialize)]
struct TokenResponse {
    access_token: Option<String>,
    expires_in: Option<u64>,
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
                    ("assertion", &assertion),
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
        let (Some(mut token), Some(expires_in)) = (parsed.access_token.take(), parsed.expires_in)
        else {
            return Err(ErrorCode::BadResponse);
        };
        if token.is_empty()
            || token.len() > MAX_TOKEN_BYTES
            || !token.bytes().all(|b| (0x21..=0x7e).contains(&b))
        {
            token.zeroize();
            return Err(ErrorCode::BadResponse);
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

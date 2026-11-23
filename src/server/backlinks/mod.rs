//! Client side of the `wiki_backlinks` tool: a bounded HTTP client, a Zitadel
//! JWT-profile token cache and the validated origins they talk to.
//!
//! Nothing here is reachable from a tool argument: the sidecar origin, the
//! issuer and the key file are fixed at startup by the operator.

pub mod client;
pub mod token;

use crate::server::binding::BacklinksConfig;
use crate::server::secret::{FileSecretSource, SecretSource, ZitadelKey};
use crate::server::types::{ErrorCode, MAX_PAGE_NAME_BYTES};
use client::{HttpClient, HttpConfig, HttpError};
use serde::Deserialize;
use std::sync::Arc;
use std::time::{Duration, Instant};
use token::TokenCache;
use ureq::http::Uri;

/// Largest accepted sidecar response (`MAX_PAGES` 20000 x 256-byte names fits).
const MAX_RESPONSE_BYTES: usize = 8 * 1024 * 1024;
/// Largest accepted token endpoint response.
const MAX_TOKEN_RESPONSE_BYTES: usize = 64 * 1024;
/// Connect deadline (capped by the per-call deadline).
const CONNECT_TIMEOUT: Duration = Duration::from_millis(5000);
/// Accepted per-call deadline range in milliseconds.
const TIMEOUT_RANGE_MS: std::ops::RangeInclusive<u128> = 1000..=60_000;
/// The only schema this client understands.
pub const SCHEMA_VERSION: &str = "backlinks.v1";

/// A validated `scheme://authority` with no path, query, fragment or userinfo.
///
/// `https` is required; plain `http` is accepted only for the loopback
/// literals `127.0.0.1` and `[::1]` (tests), where nothing leaves the host.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Origin(String);

/// The origin string is not an acceptable fixed origin.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidOrigin;

impl std::fmt::Display for InvalidOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("not an https origin (scheme://host[:port], no path)")
    }
}

impl std::error::Error for InvalidOrigin {}

impl Origin {
    /// Validate `s`.
    pub fn parse(s: &str) -> Result<Self, InvalidOrigin> {
        if s.is_empty() || s.len() > 256 || s.contains('#') || s.contains('?') || s.contains('@') {
            return Err(InvalidOrigin);
        }
        let uri: Uri = s.parse().map_err(|_| InvalidOrigin)?;
        let scheme = uri.scheme_str().ok_or(InvalidOrigin)?;
        let authority = uri.authority().ok_or(InvalidOrigin)?;
        if authority.as_str().contains('@') || authority.host().is_empty() {
            return Err(InvalidOrigin);
        }
        if uri.query().is_some() || (uri.path() != "/") {
            return Err(InvalidOrigin);
        }
        let loopback = matches!(authority.host(), "127.0.0.1" | "[::1]");
        match scheme {
            "https" => {}
            "http" if loopback => {}
            _ => return Err(InvalidOrigin),
        }
        Ok(Self(format!("{scheme}://{authority}")))
    }

    /// Canonical `scheme://authority` text (no trailing slash).
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// `origin + path`; `path` must start with `/`.
    pub fn join(&self, path: &str) -> String {
        debug_assert!(path.starts_with('/'));
        format!("{}{}", self.0, path)
    }
}

/// Percent-encode `s` for a URL query value or a form field (RFC 3986
/// unreserved characters pass through; everything else is `%XX`).
pub fn percent_encode(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    percent_encode_into(&mut out, s);
    out
}

/// Append the percent-encoding of `s` to `out`. No temporary strings are
/// built, so encoding a secret (the form body's assertion) leaves no copy
/// other than `out` itself.
pub fn percent_encode_into(out: &mut String, s: &str) {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    for b in s.bytes() {
        if b.is_ascii_alphanumeric() || matches!(b, b'-' | b'.' | b'_' | b'~') {
            out.push(b as char);
        } else {
            out.push('%');
            out.push(HEX[usize::from(b >> 4)] as char);
            out.push(HEX[usize::from(b & 0x0f)] as char);
        }
    }
}

/// Why a [`BacklinksService`] could not be built.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InitError {
    /// The configuration is not acceptable.
    InvalidConfig,
    /// The key file is missing, unsafe or not a usable key. Carries no path.
    Credential,
}

/// A failed sidecar exchange: a fixed code and, for an unavailable index,
/// its status (only the two known values are ever carried).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Failure {
    /// What went wrong.
    pub code: ErrorCode,
    /// `updating` or `unavailable` for [`ErrorCode::BacklinksUnavailable`].
    pub index_status: Option<&'static str>,
}

impl From<ErrorCode> for Failure {
    fn from(code: ErrorCode) -> Self {
        Self {
            code,
            index_status: None,
        }
    }
}

/// A validated `backlinks.v1` answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SidecarPage {
    /// The sidecar's repository id.
    pub repo_id: String,
    /// Echo of the requested page.
    pub page: String,
    /// Sidecar-side check time (RFC 3339).
    pub checked_at: String,
    /// Index generation.
    pub generation: u64,
    /// Source pages of all inbound links.
    pub inbound: Vec<String>,
}

#[derive(Deserialize)]
struct Wire {
    schema_version: String,
    repo_id: String,
    page: String,
    status: String,
    checked_at: String,
    generation: u64,
    inbound: Vec<WireRow>,
}

#[derive(Deserialize)]
struct WireRow {
    source_page: String,
}

#[derive(Deserialize)]
struct WireUnavailable {
    status: Option<String>,
}

/// The sidecar client of one bound repository: fixed origin, token cache,
/// bounded HTTP. Calls block; run them under `spawn_blocking`.
#[derive(Debug)]
pub struct BacklinksService {
    sidecar: Origin,
    http: HttpClient,
    tokens: TokenCache,
}

impl BacklinksService {
    /// Validate `cfg` and build the client.
    ///
    /// The key file is checked once here (exists, regular, mode, size, parses
    /// as a Zitadel key with a usable RSA key) so a deployment mistake stops
    /// the server at startup. It is read again on every token refresh, so a
    /// rotated key is still picked up, and a key that breaks later is a
    /// runtime `credential_unavailable`. No network call is made.
    pub fn new(cfg: &BacklinksConfig) -> Result<Self, InitError> {
        let sidecar = Origin::parse(&cfg.url).map_err(|_| InitError::InvalidConfig)?;
        let issuer = Origin::parse(&cfg.issuer).map_err(|_| InitError::InvalidConfig)?;
        if !TIMEOUT_RANGE_MS.contains(&cfg.timeout.as_millis())
            || cfg.key_file.as_os_str().is_empty()
            || cfg.audience_scopes.is_empty()
            || !cfg.audience_scopes.iter().all(|s| {
                !s.is_empty() && s.len() <= 256 && s.bytes().all(|b| (0x21..=0x7e).contains(&b))
            })
        {
            return Err(InitError::InvalidConfig);
        }
        let source = FileSecretSource::new(&cfg.key_file);
        let raw = source.read().map_err(|_| InitError::Credential)?;
        let key = ZitadelKey::parse(&raw).map_err(|_| InitError::Credential)?;
        token::check_signing_key(&key).map_err(|_| InitError::Credential)?;
        drop((raw, key));
        let connect_timeout = CONNECT_TIMEOUT.min(cfg.timeout);
        let token_http = Arc::new(HttpClient::new(HttpConfig {
            timeout: cfg.timeout,
            connect_timeout,
            max_body: MAX_TOKEN_RESPONSE_BYTES,
        }));
        let http = HttpClient::new(HttpConfig {
            timeout: cfg.timeout,
            connect_timeout,
            max_body: MAX_RESPONSE_BYTES,
        });
        let tokens = TokenCache::new(
            Arc::new(source),
            token_http,
            issuer,
            cfg.audience_scopes.clone(),
        );
        Ok(Self {
            sidecar,
            http,
            tokens,
        })
    }

    /// Fetch the inbound links of `page`. A 401 triggers exactly one forced
    /// token refresh and one retry.
    pub fn fetch(&self, page: &str) -> Result<SidecarPage, Failure> {
        let url = self
            .sidecar
            .join(&format!("/v1/backlinks?name={}", percent_encode(page)));
        let token = self.tokens.get()?;
        let mut resp = self.get(&url, &token)?;
        if resp.status == 401 {
            let fresh = self.tokens.refresh_rejected(&token)?;
            resp = self.get(&url, &fresh)?;
            if resp.status == 401 {
                return Err(ErrorCode::BacklinksAuthFailed.into());
            }
        }
        match resp.status {
            200 => parse_page(&resp.body),
            400 => Err(ErrorCode::InvalidArgument.into()),
            403 => Err(ErrorCode::BacklinksForbidden.into()),
            404 => Err(ErrorCode::PageNotFound.into()),
            503 => Err(Failure {
                code: ErrorCode::BacklinksUnavailable,
                index_status: unavailable_status(&resp.body),
            }),
            500..=599 => Err(ErrorCode::BacklinksUnreachable.into()),
            _ => Err(ErrorCode::BadResponse.into()),
        }
    }

    fn get(&self, url: &str, token: &token::Token) -> Result<client::HttpResponse, Failure> {
        let started = Instant::now();
        let resp = self
            .http
            .get(url, Some(token.secret()))
            .map_err(|e| match e {
                HttpError::Timeout => ErrorCode::Timeout,
                HttpError::Unreachable => ErrorCode::BacklinksUnreachable,
                HttpError::TooLarge | HttpError::Protocol => ErrorCode::BadResponse,
            })?;
        tracing::debug!(
            status = resp.status,
            elapsed_ms = started.elapsed().as_millis() as u64,
            "backlinks sidecar answered"
        );
        Ok(resp)
    }
}

fn unavailable_status(body: &[u8]) -> Option<&'static str> {
    let w: WireUnavailable = serde_json::from_slice(body).ok()?;
    match w.status.as_deref() {
        Some("updating") => Some("updating"),
        Some("unavailable") => Some("unavailable"),
        _ => None,
    }
}

fn parse_page(body: &[u8]) -> Result<SidecarPage, Failure> {
    let bad = || Failure::from(ErrorCode::BadResponse);
    let w: Wire = serde_json::from_slice(body).map_err(|_| bad())?;
    if w.schema_version != SCHEMA_VERSION
        || w.status != "current"
        || w.checked_at.is_empty()
        || w.checked_at.len() > 64
        || w.page.is_empty()
        || w.page.len() > MAX_PAGE_NAME_BYTES
        || w.repo_id.len() > 64
        || w.inbound
            .iter()
            .any(|r| r.source_page.is_empty() || r.source_page.len() > MAX_PAGE_NAME_BYTES)
    {
        return Err(bad());
    }
    Ok(SidecarPage {
        repo_id: w.repo_id,
        page: w.page,
        checked_at: w.checked_at,
        generation: w.generation,
        inbound: w.inbound.into_iter().map(|r| r.source_page).collect(),
    })
}

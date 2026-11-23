//! Client side of the `wiki_backlinks` tool: a bounded HTTP client, a Zitadel
//! JWT-profile token cache and the validated origins they talk to.
//!
//! Nothing here is reachable from a tool argument: the sidecar origin, the
//! issuer and the key file are fixed at startup by the operator.

pub mod client;
pub mod token;

use ureq::http::Uri;

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
    for b in s.bytes() {
        if b.is_ascii_alphanumeric() || matches!(b, b'-' | b'.' | b'_' | b'~') {
            out.push(b as char);
        } else {
            out.push_str(&format!("%{b:02X}"));
        }
    }
    out
}

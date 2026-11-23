//! Bounded blocking HTTP client (ureq, rustls, WebPKI roots).
//!
//! Every call has a global deadline (it also covers reading the body) and a
//! response-size cap. Redirects are not followed, the environment's proxy
//! settings are ignored, and error statuses are returned, not raised, so the
//! caller maps them. Errors are a closed enum: no URL, header or body text
//! survives into it. Calls block: run them under `spawn_blocking`.

use super::percent_encode_into;
use crate::server::secret::Secret;
use std::io::Read;
use std::time::Duration;
use zeroize::Zeroizing;

/// Size of the stack buffer a body is read through.
const READ_CHUNK: usize = 8 * 1024;

/// Limits of one [`HttpClient`].
#[derive(Debug, Clone, Copy)]
pub struct HttpConfig {
    /// Deadline of one call, connect through the last body byte.
    pub timeout: Duration,
    /// Deadline of the TCP/TLS connect.
    pub connect_timeout: Duration,
    /// Largest accepted response body in bytes.
    pub max_body: usize,
}

/// Transport failure classes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HttpError {
    /// The deadline passed.
    Timeout,
    /// Connect, DNS or TLS failed, or the peer dropped the connection.
    Unreachable,
    /// The body exceeded the cap.
    TooLarge,
    /// The exchange was not valid HTTP.
    Protocol,
}

/// A completed exchange: any status, bounded body.
///
/// The body may be a token response, so it is wiped on drop and `Debug` shows
/// its length only.
pub struct HttpResponse {
    /// HTTP status code.
    pub status: u16,
    /// Response body, at most the configured cap.
    pub body: Zeroizing<Vec<u8>>,
}

impl std::fmt::Debug for HttpResponse {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("HttpResponse")
            .field("status", &self.status)
            .field("body_len", &self.body.len())
            .finish()
    }
}

/// Blocking client with fixed limits.
pub struct HttpClient {
    agent: ureq::Agent,
    max_body: u64,
}

impl std::fmt::Debug for HttpClient {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("HttpClient")
            .field("max_body", &self.max_body)
            .finish_non_exhaustive()
    }
}

impl HttpClient {
    /// Build a client. TLS verification cannot be disabled; plain `http` only
    /// ever reaches a loopback host because origins are validated first.
    pub fn new(cfg: HttpConfig) -> Self {
        let agent: ureq::Agent = ureq::Agent::config_builder()
            .timeout_global(Some(cfg.timeout))
            .timeout_connect(Some(cfg.connect_timeout))
            .max_redirects(0)
            .max_redirects_will_error(false)
            .http_status_as_error(false)
            .proxy(None)
            .https_only(false)
            .build()
            .into();
        Self {
            agent,
            max_body: cfg.max_body as u64,
        }
    }

    /// `GET url` with `Accept: application/json` and an optional bearer.
    pub fn get(&self, url: &str, bearer: Option<&Secret>) -> Result<HttpResponse, HttpError> {
        let mut req = self.agent.get(url).header("Accept", "application/json");
        let header: Option<Zeroizing<String>> = match bearer {
            Some(s) => Some(Zeroizing::new(format!(
                "Bearer {}",
                std::str::from_utf8(s.expose()).map_err(|_| HttpError::Protocol)?
            ))),
            None => None,
        };
        if let Some(h) = &header {
            req = req.header("Authorization", h.as_str());
        }
        self.finish(req.call())
    }

    /// `POST url` as `application/x-www-form-urlencoded`.
    pub fn post_form(&self, url: &str, fields: &[(&str, &str)]) -> Result<HttpResponse, HttpError> {
        // The body carries the signed assertion. It is built in one buffer
        // sized for the worst case (every byte `%XX`) so it never reallocates
        // and leaves a stale copy behind, and it is wiped when this returns.
        // ureq copies it again into its own send buffer (not reachable).
        let cap: usize = fields
            .iter()
            .map(|(k, v)| 3 * (k.len() + v.len()) + 2)
            .sum();
        let mut body = Zeroizing::new(String::with_capacity(cap));
        for (i, (k, v)) in fields.iter().enumerate() {
            if i > 0 {
                body.push('&');
            }
            percent_encode_into(&mut body, k);
            body.push('=');
            percent_encode_into(&mut body, v);
        }
        let res = self
            .agent
            .post(url)
            .header("Accept", "application/json")
            .header("Content-Type", "application/x-www-form-urlencoded")
            .send(body.as_bytes());
        self.finish(res)
    }

    fn finish(
        &self,
        res: Result<ureq::http::Response<ureq::Body>, ureq::Error>,
    ) -> Result<HttpResponse, HttpError> {
        let mut resp = res.map_err(classify)?;
        let status = resp.status().as_u16();
        let mut reader = resp.body_mut().with_config().limit(self.max_body).reader();
        let body = read_wiping(&mut reader, self.max_body as usize)?;
        Ok(HttpResponse { status, body })
    }
}

/// Read `reader` to the end into a buffer that is wiped on drop, including
/// when a read fails half way. The buffer grows by copy-then-wipe, so no
/// abandoned reallocation keeps body bytes. (`read_to_end` would leave the
/// old allocation behind on every growth.) Bytes ureq itself buffers while
/// decoding the chunked/length framing are outside this crate's reach.
fn read_wiping(reader: &mut impl Read, cap: usize) -> Result<Zeroizing<Vec<u8>>, HttpError> {
    let mut chunk = Zeroizing::new([0u8; READ_CHUNK]);
    let mut buf: Zeroizing<Vec<u8>> = Zeroizing::new(Vec::with_capacity(READ_CHUNK));
    loop {
        let n = match reader.read(&mut chunk[..]) {
            Ok(0) => return Ok(buf),
            Ok(n) => n,
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(classify(ureq::Error::from(e))),
        };
        if buf.len() + n > cap {
            return Err(HttpError::TooLarge);
        }
        if buf.capacity() - buf.len() < n {
            let want = (buf.capacity() * 2).max(buf.len() + n);
            let mut bigger = Zeroizing::new(Vec::with_capacity(want));
            bigger.extend_from_slice(&buf);
            buf = bigger; // the old buffer is wiped as it drops here
        }
        buf.extend_from_slice(&chunk[..n]);
    }
}

fn classify(e: ureq::Error) -> HttpError {
    use std::io::ErrorKind;
    match e {
        ureq::Error::Timeout(_) | ureq::Error::BodyStalled => HttpError::Timeout,
        ureq::Error::BodyExceedsLimit(_) => HttpError::TooLarge,
        ureq::Error::Io(io) => match io.kind() {
            ErrorKind::TimedOut | ErrorKind::WouldBlock => HttpError::Timeout,
            _ => HttpError::Unreachable,
        },
        ureq::Error::HostNotFound
        | ureq::Error::ConnectionFailed
        | ureq::Error::Tls(_)
        | ureq::Error::Rustls(_)
        | ureq::Error::Pem(_) => HttpError::Unreachable,
        _ => HttpError::Protocol,
    }
}

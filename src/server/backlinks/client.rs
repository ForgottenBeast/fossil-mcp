//! Bounded blocking HTTP client (ureq, rustls, WebPKI roots).
//!
//! Every call has a global deadline (it also covers reading the body) and a
//! response-size cap. Redirects are not followed, the environment's proxy
//! settings are ignored, and error statuses are returned, not raised, so the
//! caller maps them. Errors are a closed enum: no URL, header or body text
//! survives into it. Calls block: run them under `spawn_blocking`.

use super::percent_encode;
use crate::server::secret::Secret;
use std::time::Duration;
use zeroize::Zeroizing;

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
#[derive(Debug)]
pub struct HttpResponse {
    /// HTTP status code.
    pub status: u16,
    /// Response body, at most the configured cap.
    pub body: Vec<u8>,
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
        let body: String = fields
            .iter()
            .map(|(k, v)| format!("{}={}", percent_encode(k), percent_encode(v)))
            .collect::<Vec<_>>()
            .join("&");
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
        let body = resp
            .body_mut()
            .with_config()
            .limit(self.max_body)
            .read_to_vec()
            .map_err(classify)?;
        Ok(HttpResponse { status, body })
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

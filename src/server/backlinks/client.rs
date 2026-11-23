//! Bounded blocking HTTP/1.1 client (hyper, rustls with ring, WebPKI roots).
//!
//! Why hyper and not a batteries-included client: the request carries a bearer
//! token and a signed assertion, and the previous client's protocol crate
//! hex-dumped raw request bytes at TRACE through `log`. A `log` level feature
//! (`release_max_level_*`) set by any downstream crate overrides a cap set
//! here, so the cap was never a guarantee. This stack has no code path that
//! logs bytes at all: hyper's `tracing` feature (unstable, off by default) is
//! not enabled, rustls is built without its `logging` feature, and nothing
//! else in the graph logs. `tests/dependency_hygiene.rs` pins that in the
//! lockfile and `tests/backlinks_log.rs` proves it under a catch-all logger
//! and subscriber.
//!
//! Every call has a global deadline (it also covers reading the body) and a
//! response-size cap enforced while reading. Redirects are not followed (hyper
//! never does), the environment's proxy settings are never read, error
//! statuses are returned, not raised, and one connection serves one call.
//! Errors are a closed enum: no URL, header or body text survives into it.
//! Calls block (a private current-thread runtime drives each one, on a scoped
//! thread when the caller is inside a tokio runtime): run them under
//! `spawn_blocking`, never directly on an async worker.

use super::percent_encode_into;
use crate::server::secret::Secret;
use http_body_util::{BodyExt, Full};
use hyper::body::{Bytes, Incoming};
use hyper::header::{ACCEPT, AUTHORIZATION, CONNECTION, CONTENT_LENGTH, CONTENT_TYPE, HOST};
use hyper::http::HeaderValue;
use hyper::{Method, Request, Uri};
use hyper_util::rt::TokioIo;
use rustls::pki_types::ServerName;
use std::sync::Arc;
use std::time::Duration;
use tokio::net::TcpStream;
use tokio::time::timeout;
use tokio_rustls::TlsConnector;
use zeroize::Zeroizing;

/// Initial capacity of a body buffer.
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
    cfg: HttpConfig,
    tls: TlsConnector,
}

impl std::fmt::Debug for HttpClient {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("HttpClient")
            .field("max_body", &self.cfg.max_body)
            .finish_non_exhaustive()
    }
}

/// What one call sends.
struct Call<'a> {
    method: Method,
    url: &'a str,
    authorization: Option<HeaderValue>,
    content_type: Option<&'static str>,
    body: Bytes,
}

/// `Authorization: Bearer <token>` marked sensitive, so no `Debug` output of
/// the request or its headers (hyper's or anyone's) can show it.
pub(crate) fn bearer_header(token: &Secret) -> Result<HeaderValue, HttpError> {
    let mut raw = Zeroizing::new(Vec::with_capacity(7 + token.expose().len()));
    raw.extend_from_slice(b"Bearer ");
    raw.extend_from_slice(token.expose());
    // The header value takes over the wiping buffer itself: `from_bytes` would
    // copy it into a fresh allocation that is freed unwiped. A rejected value
    // (CR/LF or other invalid bytes) drops the owner, which wipes it.
    let mut value =
        HeaderValue::from_maybe_shared(Bytes::from_owner(raw)).map_err(|_| HttpError::Protocol)?;
    value.set_sensitive(true);
    Ok(value)
}

impl HttpClient {
    /// Build a client. TLS verification cannot be disabled; plain `http` only
    /// ever reaches a loopback host because origins are validated first.
    pub fn new(cfg: HttpConfig) -> Self {
        let roots = rustls::RootCertStore {
            roots: webpki_roots::TLS_SERVER_ROOTS.to_vec(),
        };
        let mut tls = rustls::ClientConfig::builder_with_provider(Arc::new(
            rustls::crypto::ring::default_provider(),
        ))
        .with_safe_default_protocol_versions()
        .expect("ring supports the default protocol versions")
        .with_root_certificates(roots)
        .with_no_client_auth();
        tls.alpn_protocols = vec![b"http/1.1".to_vec()];
        Self {
            cfg,
            tls: TlsConnector::from(Arc::new(tls)),
        }
    }

    /// `GET url` with `Accept: application/json` and an optional bearer.
    pub fn get(&self, url: &str, bearer: Option<&Secret>) -> Result<HttpResponse, HttpError> {
        let authorization = bearer.map(bearer_header).transpose()?;
        self.call(Call {
            method: Method::GET,
            url,
            authorization,
            content_type: None,
            body: Bytes::new(),
        })
    }

    /// `POST url` as `application/x-www-form-urlencoded`.
    pub fn post_form(&self, url: &str, fields: &[(&str, &str)]) -> Result<HttpResponse, HttpError> {
        // The body carries the signed assertion. It is built in one buffer
        // sized for the worst case (every byte `%XX`) so it never reallocates
        // and leaves a stale copy behind. That same buffer is handed to hyper
        // as the request body (`Bytes::from_owner`), so no second copy is made
        // here and it is wiped when the last reference to it is dropped. What
        // hyper copies into its own write buffer is not reachable from this
        // crate and is an accepted gap.
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
        self.call(Call {
            method: Method::POST,
            url,
            authorization: None,
            content_type: Some("application/x-www-form-urlencoded"),
            body: Bytes::from_owner(Zeroizing::new(std::mem::take(&mut *body).into_bytes())),
        })
    }

    fn call(&self, call: Call<'_>) -> Result<HttpResponse, HttpError> {
        // `Runtime::block_on` panics when this thread already drives a tokio
        // runtime (an async task, or a `#[tokio::main]` body). A thread that
        // belongs to a runtime cannot be told apart from a `spawn_blocking`
        // thread, where blocking is legitimate, so refusing would break the
        // supported caller. Run on a fresh scoped thread instead, which has no
        // runtime context: it never panics and the result is the same. The
        // call still blocks the calling thread, so async callers should keep
        // using `spawn_blocking`.
        if tokio::runtime::Handle::try_current().is_ok() {
            return std::thread::scope(|s| {
                s.spawn(|| self.call_blocking(call))
                    .join()
                    .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
            });
        }
        self.call_blocking(call)
    }

    fn call_blocking(&self, call: Call<'_>) -> Result<HttpResponse, HttpError> {
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_io()
            .enable_time()
            .build()
            .map_err(|_| HttpError::Protocol)?;
        let out = rt.block_on(async {
            timeout(self.cfg.timeout, self.exchange(call))
                .await
                .unwrap_or(Err(HttpError::Timeout))
        });
        // Do not wait for a lookup thread that outlived the deadline.
        rt.shutdown_background();
        out
    }

    async fn exchange(&self, call: Call<'_>) -> Result<HttpResponse, HttpError> {
        let uri: Uri = call.url.parse().map_err(|_| HttpError::Protocol)?;
        let https = match uri.scheme_str() {
            Some("https") => true,
            Some("http") => false,
            _ => return Err(HttpError::Protocol),
        };
        let authority = uri.authority().ok_or(HttpError::Protocol)?.clone();
        let host = authority.host().trim_matches(['[', ']']).to_owned();
        let port = authority.port_u16().unwrap_or(if https { 443 } else { 80 });
        let target = uri.path_and_query().map_or("/", |p| p.as_str()).to_owned();

        let mut req = Request::builder()
            .method(call.method)
            .uri(target)
            .header(HOST, authority.as_str())
            .header(ACCEPT, "application/json")
            .header(CONNECTION, "close");
        if let Some(ct) = call.content_type {
            req = req
                .header(CONTENT_TYPE, ct)
                .header(CONTENT_LENGTH, call.body.len());
        }
        if let Some(auth) = call.authorization {
            req = req.header(AUTHORIZATION, auth);
        }
        let req = req
            .body(Full::new(call.body))
            .map_err(|_| HttpError::Protocol)?;

        let connect = async {
            let tcp = TcpStream::connect((host.as_str(), port))
                .await
                .map_err(|_| HttpError::Unreachable)?;
            tcp.set_nodelay(true).ok();
            if !https {
                return Ok(Stream::Plain(tcp));
            }
            let name = ServerName::try_from(host.clone()).map_err(|_| HttpError::Unreachable)?;
            let tls = self
                .tls
                .connect(name, tcp)
                .await
                .map_err(|_| HttpError::Unreachable)?;
            Ok(Stream::Tls(Box::new(tls)))
        };
        let stream = timeout(self.cfg.connect_timeout, connect)
            .await
            .map_err(|_| HttpError::Timeout)??;
        match stream {
            Stream::Plain(s) => send(TokioIo::new(s), req, self.cfg.max_body).await,
            Stream::Tls(s) => send(TokioIo::new(s), req, self.cfg.max_body).await,
        }
    }
}

enum Stream {
    Plain(TcpStream),
    Tls(Box<tokio_rustls::client::TlsStream<TcpStream>>),
}

/// One HTTP/1.1 exchange over `io`.
async fn send<I>(io: I, req: Request<Full<Bytes>>, cap: usize) -> Result<HttpResponse, HttpError>
where
    I: hyper::rt::Read + hyper::rt::Write + Unpin + Send + 'static,
{
    let (mut sender, conn) = hyper::client::conn::http1::handshake(io)
        .await
        .map_err(classify)?;
    let driver = tokio::spawn(conn);
    let result = async {
        let resp = sender.send_request(req).await.map_err(classify)?;
        let status = resp.status().as_u16();
        let body = read_capped(resp.into_body(), cap).await?;
        Ok(HttpResponse { status, body })
    }
    .await;
    driver.abort();
    result
}

/// Read `body` to the end into a buffer that is wiped on drop, including
/// when a read fails half way, refusing to hold more than `cap` bytes. The
/// buffer grows by copy-then-wipe, so no abandoned reallocation keeps body
/// bytes. (Chunks hyper itself buffers while decoding the framing are outside
/// this crate's reach.)
async fn read_capped(mut body: Incoming, cap: usize) -> Result<Zeroizing<Vec<u8>>, HttpError> {
    let mut buf: Zeroizing<Vec<u8>> = Zeroizing::new(Vec::with_capacity(READ_CHUNK));
    while let Some(frame) = body.frame().await {
        let frame = frame.map_err(classify)?;
        let Ok(data) = frame.into_data() else {
            continue; // trailers
        };
        if buf.len() + data.len() > cap {
            return Err(HttpError::TooLarge);
        }
        if buf.capacity() - buf.len() < data.len() {
            let want = (buf.capacity() * 2).max(buf.len() + data.len());
            let mut bigger = Zeroizing::new(Vec::with_capacity(want));
            bigger.extend_from_slice(&buf);
            buf = bigger; // the old buffer is wiped as it drops here
        }
        buf.extend_from_slice(&data);
    }
    Ok(buf)
}

fn classify(e: hyper::Error) -> HttpError {
    if e.is_timeout() {
        HttpError::Timeout
    } else if e.is_incomplete_message() || e.is_closed() || e.is_canceled() {
        HttpError::Unreachable
    } else {
        HttpError::Protocol
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bearer_header_is_sensitive_and_never_debug_printed() {
        let h = bearer_header(&Secret::new(b"SENTINEL-BEARER".to_vec())).unwrap();
        assert!(h.is_sensitive());
        assert_eq!(h.as_bytes(), b"Bearer SENTINEL-BEARER");
        assert!(!format!("{h:?}").contains("SENTINEL"));
    }

    #[test]
    fn bearer_header_rejects_bytes_that_could_split_the_header() {
        assert!(bearer_header(&Secret::new(b"a\r\nX: y".to_vec())).is_err());
    }
}

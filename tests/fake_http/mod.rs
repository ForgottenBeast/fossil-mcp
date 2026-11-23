//! A tiny loopback HTTP/1.1 server for tests (issuer and sidecar fakes).
//! One thread per connection, `Connection: close`, every request recorded.
#![allow(dead_code)]

use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

/// One recorded request.
#[derive(Debug, Clone)]
pub struct Req {
    pub method: String,
    pub target: String,
    pub headers: Vec<(String, String)>,
    pub body: Vec<u8>,
}

impl Req {
    pub fn header(&self, name: &str) -> Option<&str> {
        self.headers
            .iter()
            .find(|(k, _)| k.eq_ignore_ascii_case(name))
            .map(|(_, v)| v.as_str())
    }
}

/// What the fake answers.
pub enum Reply {
    /// A complete response.
    Full { status: u16, body: Vec<u8> },
    /// Headers promise more body than is ever sent, then the socket idles.
    Stall { status: u16, stall: Duration },
}

impl Reply {
    pub fn json(status: u16, v: serde_json::Value) -> Self {
        Reply::Full {
            status,
            body: v.to_string().into_bytes(),
        }
    }
}

type Handler = dyn Fn(&Req, usize) -> Reply + Send + Sync;

pub struct Fake {
    pub addr: SocketAddr,
    log: Arc<Mutex<Vec<Req>>>,
    stop: Arc<AtomicBool>,
}

impl Fake {
    /// `handler(request, zero_based_request_index)`.
    pub fn start(handler: impl Fn(&Req, usize) -> Reply + Send + Sync + 'static) -> Self {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap();
        let log = Arc::new(Mutex::new(Vec::new()));
        let stop = Arc::new(AtomicBool::new(false));
        let handler: Arc<Handler> = Arc::new(handler);
        let (l2, s2) = (log.clone(), stop.clone());
        std::thread::spawn(move || {
            for conn in listener.incoming() {
                if s2.load(Ordering::SeqCst) {
                    break;
                }
                let Ok(conn) = conn else { continue };
                let (h, l) = (handler.clone(), l2.clone());
                std::thread::spawn(move || serve(conn, &*h, &l));
            }
        });
        Fake { addr, log, stop }
    }

    /// `http://127.0.0.1:<port>`
    pub fn url(&self) -> String {
        format!("http://{}", self.addr)
    }

    pub fn requests(&self) -> Vec<Req> {
        self.log.lock().unwrap().clone()
    }

    pub fn count(&self) -> usize {
        self.log.lock().unwrap().len()
    }
}

impl Drop for Fake {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::SeqCst);
        let _ = TcpStream::connect(self.addr);
    }
}

fn read_request(conn: &mut TcpStream) -> Option<Req> {
    conn.set_read_timeout(Some(Duration::from_secs(10))).ok()?;
    let mut buf = Vec::new();
    let mut chunk = [0u8; 4096];
    let head_end = loop {
        if let Some(p) = buf.windows(4).position(|w| w == b"\r\n\r\n") {
            break p;
        }
        let n = conn.read(&mut chunk).ok()?;
        if n == 0 {
            return None;
        }
        buf.extend_from_slice(&chunk[..n]);
    };
    let head = String::from_utf8_lossy(&buf[..head_end]).into_owned();
    let mut lines = head.split("\r\n");
    let mut first = lines.next()?.split(' ');
    let method = first.next()?.to_string();
    let target = first.next()?.to_string();
    let headers: Vec<(String, String)> = lines
        .filter_map(|l| l.split_once(':'))
        .map(|(k, v)| (k.trim().to_string(), v.trim().to_string()))
        .collect();
    let want: usize = headers
        .iter()
        .find(|(k, _)| k.eq_ignore_ascii_case("content-length"))
        .and_then(|(_, v)| v.parse().ok())
        .unwrap_or(0);
    let mut body = buf[head_end + 4..].to_vec();
    while body.len() < want {
        let n = conn.read(&mut chunk).ok()?;
        if n == 0 {
            return None;
        }
        body.extend_from_slice(&chunk[..n]);
    }
    Some(Req {
        method,
        target,
        headers,
        body,
    })
}

fn serve(mut conn: TcpStream, handler: &Handler, log: &Mutex<Vec<Req>>) {
    let Some(req) = read_request(&mut conn) else {
        return;
    };
    let idx = {
        let mut l = log.lock().unwrap();
        l.push(req.clone());
        l.len() - 1
    };
    match handler(&req, idx) {
        Reply::Full { status, body } => {
            let head = format!(
                "HTTP/1.1 {status} X\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
                body.len()
            );
            let _ = conn.write_all(head.as_bytes());
            let _ = conn.write_all(&body);
        }
        Reply::Stall { status, stall } => {
            let head = format!(
                "HTTP/1.1 {status} X\r\nContent-Type: application/json\r\nContent-Length: 1000000\r\nConnection: close\r\n\r\n{{"
            );
            let _ = conn.write_all(head.as_bytes());
            let _ = conn.flush();
            std::thread::sleep(stall);
        }
    }
}

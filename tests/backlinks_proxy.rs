//! The client never reads proxy settings from the environment: the bearer
//! token goes to the configured origin only, whatever `*_PROXY` says.
//! Its own test binary because it edits the process environment.
mod fake_http;

use fake_http::{Fake, Reply};
use fossil_mcp::server::backlinks::client::{HttpClient, HttpConfig};
use fossil_mcp::server::secret::Secret;
use serde_json::json;
use std::time::Duration;

#[test]
fn proxy_environment_is_ignored() {
    let proxy = Fake::start(|_, _| Reply::json(200, json!({"via":"proxy"})));
    let origin = Fake::start(|_, _| Reply::json(200, json!({"via":"origin"})));
    for name in [
        "HTTP_PROXY",
        "http_proxy",
        "HTTPS_PROXY",
        "https_proxy",
        "ALL_PROXY",
        "all_proxy",
    ] {
        // SAFETY: no other thread of this test binary touches the
        // environment, and the client is not running yet.
        unsafe { std::env::set_var(name, proxy.url()) };
    }
    unsafe {
        std::env::remove_var("NO_PROXY");
        std::env::remove_var("no_proxy");
    }
    let client = HttpClient::new(HttpConfig {
        timeout: Duration::from_secs(5),
        connect_timeout: Duration::from_secs(2),
        max_body: 4096,
    });
    let token = Secret::new(b"PROXY-TEST-TOKEN".to_vec());
    let r = client.get(&origin.url(), Some(&token)).unwrap();
    assert_eq!(&r.body[..], br#"{"via":"origin"}"#);
    assert_eq!(origin.count(), 1);
    assert_eq!(proxy.count(), 0, "request went through the env proxy");
}

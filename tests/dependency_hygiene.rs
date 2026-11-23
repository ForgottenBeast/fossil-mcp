//! Manifest and lockfile hygiene for the backlinks client: no unused
//! dependency, and an HTTP stack that has no logging call to switch on.

const MANIFEST: &str = include_str!("../Cargo.toml");

fn dependency_line(name: &str) -> Option<&'static str> {
    MANIFEST
        .lines()
        .find(|l| l.trim_start().starts_with(&format!("{name} ")))
}

#[test]
fn base64_is_not_a_dependency() {
    assert!(dependency_line("base64").is_none(), "unused base64");
}

#[test]
fn http_stack_is_hyper_without_its_tracing_feature() {
    assert!(dependency_line("ureq").is_none(), "ureq logs raw bytes");
    let hyper = dependency_line("hyper").expect("hyper dependency");
    assert!(!hyper.contains("tracing"), "hyper tracing is on: {hyper}");
    assert!(
        hyper.contains("http1") && hyper.contains("client"),
        "{hyper}"
    );
    assert!(!hyper.contains("http2"), "{hyper}");
}

#[test]
fn test_key_fixture_is_labelled_test_only() {
    let readme = include_str!("fixtures/README.md");
    assert!(readme.contains("test-rsa-private.pem"));
    assert!(readme.to_lowercase().contains("throwaway"));
    assert!(readme.to_lowercase().contains("never be reused"));
}

const LOCK: &str = include_str!("../Cargo.lock");

fn locked(name: &str) -> bool {
    LOCK.contains(&format!("\nname = \"{name}\"\n"))
}

#[test]
fn rsa_crate_is_not_in_the_lockfile() {
    // RUSTSEC-2023-0071 (Marvin timing attack on `rsa` private-key
    // operations): assertions are signed with ring instead.
    assert!(!locked("rsa"), "rsa crate is locked");
    assert!(!locked("jsonwebtoken"), "jsonwebtoken is locked");
    assert!(locked("ring"));
}

/// Dependencies named in the lockfile entry of `package`.
fn lock_deps(package: &str) -> Vec<String> {
    let block = LOCK
        .split("[[package]]")
        .find(|b| b.contains(&format!("\nname = \"{package}\"\n")))
        .unwrap_or_else(|| panic!("{package} is not locked"));
    block
        .lines()
        .skip_while(|l| !l.starts_with("dependencies"))
        .skip(1)
        .take_while(|l| l.starts_with(' '))
        .map(|l| l.trim().trim_matches(|c| c == '"' || c == ',').to_owned())
        .collect()
}

#[test]
fn ureq_and_its_raw_byte_logging_are_not_locked() {
    // ureq-proto prints raw request bytes (bearer, assertion) at TRACE
    // through `log`, and `log`'s release_max_level_* features override any
    // cap this crate sets, so the only guarantee is not to ship it.
    assert!(!locked("ureq"), "ureq is locked");
    assert!(!locked("ureq-proto"), "ureq-proto is locked");
}

#[test]
fn no_http_crate_can_log() {
    // A crate lists `log` or `tracing` in the lockfile only when one of its
    // features that pulls it in is enabled, so this is a feature check too:
    // hyper's unstable `tracing` and rustls's `logging` must stay off.
    for krate in [
        "hyper",
        "hyper-util",
        "http",
        "http-body",
        "http-body-util",
        "httparse",
        "tokio-rustls",
        "rustls",
        "rustls-webpki",
        "webpki-roots",
    ] {
        let deps = lock_deps(krate);
        for banned in ["log", "tracing"] {
            assert!(
                !deps
                    .iter()
                    .any(|d| d == banned || d.starts_with(&format!("{banned} "))),
                "{krate} depends on {banned}: {deps:?}"
            );
        }
    }
}

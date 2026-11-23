//! Manifest and lockfile hygiene for the backlinks client: no unused
//! dependency and no unused ureq feature.

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
fn ureq_does_not_enable_the_json_feature() {
    let ureq = dependency_line("ureq").expect("ureq dependency");
    assert!(ureq.contains("rustls"), "{ureq}");
    assert!(!ureq.contains("json"), "unused ureq json feature: {ureq}");
}

#[test]
fn test_key_fixture_is_labelled_test_only() {
    let readme = include_str!("fixtures/README.md");
    assert!(readme.contains("test-rsa-private.pem"));
    assert!(readme.to_lowercase().contains("throwaway"));
    assert!(readme.to_lowercase().contains("never be reused"));
}

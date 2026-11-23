//! Property tests: write bytes reach `fossil` via stdin, never via shared files,
//! and size/shape limits are enforced before any child is spawned.
mod common;
use common::{FakeFossil, bound, parse, wargs};
use fossil_mcp::server::types::{MAX_CONTENT_BYTES, Publication};
use proptest::prelude::*;

fn rt() -> tokio::runtime::Runtime {
    tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(24))]

    /// A/B vs A_B style names must not alias, and stdin must be exact.
    #[test]
    fn stdin_isolation(name in "[A-Za-z0-9_/]{1,24}", content in ".{0,2000}") {
        prop_assume!(!name.starts_with('-'));
        rt().block_on(async {
            let f = FakeFossil::new();
            let w = bound(&f, |_| {}).await;
            let _ = w.write_wiki_page(wargs("op1", &name, &content, Publication::LocalOnly)).await;
            let calls = f.calls_to("create");
            prop_assert_eq!(calls.len(), 1);
            let (argv, stdin) = &calls[0];
            prop_assert!(argv.iter().all(|a| !a.starts_with("/tmp/") && !a.ends_with(".txt")));
            prop_assert_eq!(stdin.as_slice(), content.as_bytes());
            Ok(())
        })?;
    }

    /// Invalid shapes never spawn a mutating child and carry a fixed error.
    #[test]
    fn invalid_input_spawns_nothing(
        op in "[ -~]{0,80}",
        name in "[ -~]{0,300}",
        extra in 0usize..3,
    ) {
        let op_ok = !op.is_empty() && op.len() <= 64
            && op.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-');
        let name_ok = !name.is_empty() && name.len() <= 256 && !name.starts_with('-');
        prop_assume!(!(op_ok && name_ok));
        let content = "x".repeat(extra);
        rt().block_on(async {
            let f = FakeFossil::new();
            let w = bound(&f, |_| {}).await;
            let r = w.write_wiki_page(wargs(&op, &name, &content, Publication::LocalOnly)).await.unwrap();
            prop_assert_eq!(r.is_error, Some(true));
            let out = parse(&r);
            prop_assert_eq!(out.error_code, Some(fossil_mcp::server::types::ErrorCode::InvalidArgument));
            prop_assert!(f.calls_to("create").is_empty() && f.calls_to("commit").is_empty());
            Ok(())
        })?;
    }
}

#[tokio::test]
async fn input_limits_are_byte_limits() {
    let f = FakeFossil::new();
    let w = bound(&f, |_| {}).await;
    // 3-byte chars: char count is under the limit, byte count is over it.
    let over = "\u{20ac}".repeat(MAX_CONTENT_BYTES / 3 + 1);
    assert!(over.chars().count() < MAX_CONTENT_BYTES && over.len() > MAX_CONTENT_BYTES);
    let r = w
        .write_wiki_page(wargs("op1", "P", &over, Publication::LocalOnly))
        .await
        .unwrap();
    assert_eq!(r.is_error, Some(true));
    assert!(f.calls_to("create").is_empty());
    let at = "a".repeat(MAX_CONTENT_BYTES);
    let r = w
        .write_wiki_page(wargs("op2", "P", &at, Publication::LocalOnly))
        .await
        .unwrap();
    assert_ne!(r.is_error, Some(true), "exactly the limit is accepted");
}

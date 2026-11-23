//! Property tests: write bytes reach `fossil` via stdin, never via shared files.
mod common;
use common::FakeFossil;
use fossil_mcp::{FossilWiki, WriteWikiPageArgs};
use proptest::prelude::*;
use rmcp::handler::server::wrapper::Parameters;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(24))]

    /// A/B vs A_B style names must not alias, and stdin must be exact.
    #[test]
    fn stdin_isolation(name in "[A-Za-z0-9_/]{1,24}", content in ".{0,2000}") {
        prop_assume!(!name.starts_with('-'));
        let rt = tokio::runtime::Builder::new_current_thread().enable_all().build().unwrap();
        rt.block_on(async {
            let f = FakeFossil::new();
            let w = FossilWiki::new(Some(f.repo_file())).with_fossil_bin(&f.bin);
            let _ = w.write_wiki_page(Parameters(WriteWikiPageArgs {
                page_name: name.clone(), content: content.clone(), mimetype: None,
                skip_sync: true, force_write: false,
            })).await;
            let calls = f.calls_to("create");
            prop_assert_eq!(calls.len(), 1);
            let (argv, stdin) = &calls[0];
            prop_assert!(argv.iter().all(|a| !a.starts_with("/tmp/") && !a.ends_with(".txt")));
            prop_assert_eq!(stdin.as_slice(), content.as_bytes());
            Ok(())
        })?;
    }
}

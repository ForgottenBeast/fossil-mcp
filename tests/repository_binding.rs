//! Immutable startup binding: validation, isolation, no runtime retargeting.
mod common;
use common::{FakeFossil, bound, real_repo};
use fossil_mcp::server::types::{ReadWikiPageArgs, WriteWikiPageArgs};
use fossil_mcp::{FossilWiki, StartupError, WikiConfig};
use proptest::prelude::*;
use rmcp::handler::server::wrapper::Parameters;

async fn bind_err(cfg: WikiConfig) -> StartupError {
    FossilWiki::bind(cfg).await.err().expect("bind must fail")
}

#[tokio::test]
async fn rejects_bad_alias_empty_file_directory_symlink_missing() {
    let f = FakeFossil::new();
    let mk = |p: std::path::PathBuf| {
        let mut c = WikiConfig::new("ok", p);
        c.fossil_bin = f.bin.clone();
        c
    };
    let mut c = mk(f.repo_file());
    c.repo_id = "bad id/..".into();
    assert_eq!(bind_err(c).await, StartupError::InvalidRepoId);
    let empty = f.dir.path().join("empty.fossil");
    std::fs::write(&empty, b"").unwrap();
    assert_eq!(
        bind_err(mk(empty)).await,
        StartupError::InvalidRepositoryFile
    );
    assert_eq!(
        bind_err(mk(f.dir.path().to_path_buf())).await,
        StartupError::InvalidRepositoryFile
    );
    assert_eq!(
        bind_err(mk(f.dir.path().join("missing"))).await,
        StartupError::InvalidRepositoryFile
    );
    let link = f.dir.path().join("link.fossil");
    std::os::unix::fs::symlink(f.repo_file(), &link).unwrap();
    assert_eq!(
        bind_err(mk(link)).await,
        StartupError::InvalidRepositoryFile
    );
}

#[tokio::test]
async fn rejects_non_repository_and_missing_fossil() {
    let (_repo, bin, dir) = real_repo();
    let junk = dir.path().join("junk.fossil");
    std::fs::write(&junk, b"definitely not sqlite").unwrap();
    let mut c = WikiConfig::new("ok", &junk);
    c.fossil_bin = bin;
    assert_eq!(bind_err(c).await, StartupError::NotAFossilRepository);
    let mut c = WikiConfig::new("ok", &junk);
    c.fossil_bin = dir.path().join("no-such-fossil");
    assert_eq!(bind_err(c).await, StartupError::FossilUnavailable);
}

#[tokio::test]
async fn two_repositories_are_isolated() {
    let (ra, bin_a, da) = real_repo();
    let (rb, bin_b, db) = real_repo();
    let mk = |r: &std::path::Path, bin: &std::path::Path, id: &str, d: &std::path::Path| {
        let mut c = WikiConfig::new(id, r);
        c.fossil_bin = bin.to_path_buf();
        c.allow_local_writes = true;
        c.state_dir = Some(d.join("state"));
        c
    };
    let a = FossilWiki::bind(mk(&ra, &bin_a, "a", da.path()))
        .await
        .unwrap();
    let b = FossilWiki::bind(mk(&rb, &bin_b, "b", db.path()))
        .await
        .unwrap();
    for (w, page) in [(&a, "OnlyInA"), (&b, "OnlyInB")] {
        let r = w
            .write_wiki_page(Parameters(WriteWikiPageArgs {
                operation_id: "o1".into(),
                page_name: page.into(),
                content: "x".into(),
                mimetype: None,
                publication: Default::default(),
            }))
            .await
            .unwrap();
        assert_ne!(r.is_error, Some(true));
    }
    assert_eq!(a.list_wiki_pages().await.unwrap().0.pages, vec!["OnlyInA"]);
    assert_eq!(b.list_wiki_pages().await.unwrap().0.pages, vec!["OnlyInB"]);
    assert!(
        a.read_wiki_page(Parameters(ReadWikiPageArgs {
            page_name: "OnlyInB".into()
        }))
        .await
        .is_err()
    );
    assert_eq!((a.repo_id(), b.repo_id()), ("a", "b"));
}

proptest! {
    /// No request-shaped input can carry a repository path or alias: every
    /// legacy/unknown field is rejected at deserialization.
    #[test]
    fn binding_cannot_change_through_requests(
        field in "(repo_path|repository|repo_id|path|db|configure)[a-z_]{0,6}",
        value in "[!-~]{8,40}",
    ) {
        let j = serde_json::json!({
            "operation_id": "o", "page_name": "P", "content": "c", field.clone(): value.clone()
        });
        let e = serde_json::from_value::<WriteWikiPageArgs>(j).unwrap_err().to_string();
        prop_assert!(!e.contains(&value), "value echoed: {}", e);
        let j = serde_json::json!({ "page_name": "P", field: value });
        prop_assert!(serde_json::from_value::<ReadWikiPageArgs>(j).is_err());
    }
}

#[tokio::test]
async fn clones_share_one_immutable_binding() {
    let f = FakeFossil::new();
    let w = bound(&f, |_| {}).await;
    let c = w.clone();
    assert_eq!(c.repo_id(), w.repo_id());
}

//! End-to-end tests against throwaway repositories made with the real `fossil`
//! binary (isolated HOME, tempdir only). A missing fossil is a failure.
mod common;
use common::{is_error, isolated_fossil, parse, real_repo, wargs};
use fossil_mcp::server::types::{
    CommitState, ErrorCode, Publication, PublicationState, ReadWikiPageArgs,
};
use fossil_mcp::{FossilWiki, WikiConfig};
use rmcp::handler::server::wrapper::Parameters;
use std::path::Path;

async fn wiki_for(repo: &Path, bin: &Path, state: &Path, sync: bool) -> FossilWiki {
    let mut cfg = WikiConfig::new("itest", repo);
    cfg.fossil_bin = bin.to_path_buf();
    cfg.allow_local_writes = true;
    cfg.allow_repository_sync = sync;
    cfg.state_dir = Some(state.join("state"));
    FossilWiki::bind(cfg).await.expect("bind")
}

fn read(p: &str) -> Parameters<ReadWikiPageArgs> {
    Parameters(ReadWikiPageArgs {
        page_name: p.into(),
    })
}

#[tokio::test]
async fn list_empty_wiki() {
    let (repo, bin, dir) = real_repo();
    let w = wiki_for(&repo, &bin, dir.path(), false).await;
    let pages = w.list_wiki_pages().await.unwrap().0.pages;
    assert!(pages.is_empty(), "{pages:?}");
}

#[tokio::test]
async fn create_then_update_proves_stdin_and_revision_chain() {
    let (repo, bin, dir) = real_repo();
    let w = wiki_for(&repo, &bin, dir.path(), false).await;
    let big = "0123456789abcdef\n".repeat(60_000); // larger than a pipe buffer
    let r1 = parse(
        &w.write_wiki_page(wargs("op1", "Notes/Page", &big, Publication::LocalOnly))
            .await
            .unwrap(),
    )
    .receipt
    .unwrap();
    assert_eq!(r1.commit_state, CommitState::Committed);
    assert_eq!(r1.previous_revision, None);
    let rev1 = r1.revision.clone().expect("attributed revision");
    let got = w.read_wiki_page(read("Notes/Page")).await.unwrap().0;
    assert_eq!(got.content, big);
    assert_eq!(
        got.revision, rev1,
        "read returns the artifact id the receipt reported"
    );

    let r2 = parse(
        &w.write_wiki_page(wargs(
            "op2",
            "Notes/Page",
            "Version 2",
            Publication::LocalOnly,
        ))
        .await
        .unwrap(),
    )
    .receipt
    .unwrap();
    assert_eq!(r2.previous_revision.as_deref(), Some(rev1.as_str()));
    let got = w.read_wiki_page(read("Notes/Page")).await.unwrap().0;
    assert_eq!(got.content, "Version 2");
    assert_eq!(Some(got.revision), r2.revision);
}

#[tokio::test]
async fn markdown_and_special_names() {
    let (repo, bin, dir) = real_repo();
    let w = wiki_for(&repo, &bin, dir.path(), false).await;
    for (i, name) in [
        "Page With Spaces",
        "caf\u{e9} \u{2603}",
        "A/B",
        "A_B",
        "x.y-z",
    ]
    .iter()
    .enumerate()
    {
        let content = format!("# {name}\n\n**bold** & <tag> \"q\" 'a' $HOME `cmd`");
        let r = w
            .write_wiki_page(wargs(
                &format!("op{i}"),
                name,
                &content,
                Publication::LocalOnly,
            ))
            .await
            .unwrap();
        assert!(!is_error(&r), "{name}");
        assert_eq!(
            w.read_wiki_page(read(name)).await.unwrap().0.content,
            content,
            "{name}"
        );
    }
    let pages = w.list_wiki_pages().await.unwrap().0.pages;
    assert!(
        pages.contains(&"A/B".to_string()) && pages.contains(&"A_B".to_string()),
        "no aliasing: {pages:?}"
    );
}

#[tokio::test]
async fn read_missing_page_is_a_fixed_error() {
    let (repo, bin, dir) = real_repo();
    let w = wiki_for(&repo, &bin, dir.path(), false).await;
    let e = w.read_wiki_page(read("Nope")).await.err().unwrap();
    assert!(e.starts_with("page_not_found:"), "{e}");
    assert!(!e.contains(repo.to_str().unwrap()), "no paths in errors");
}

#[tokio::test]
async fn real_no_remote_sync_is_pending_and_keeps_commit() {
    let (repo, bin, dir) = real_repo();
    let w = wiki_for(&repo, &bin, dir.path(), true).await;
    let r = w
        .write_wiki_page(wargs("op1", "P", "v1", Publication::SyncRepository))
        .await
        .unwrap();
    assert!(is_error(&r));
    let rc = parse(&r).receipt.unwrap();
    assert_eq!(rc.commit_state, CommitState::Committed);
    assert_eq!(rc.publication_state, PublicationState::Pending);
    assert_eq!(rc.error_code, Some(ErrorCode::NoRemote));
    assert_eq!(w.read_wiki_page(read("P")).await.unwrap().0.content, "v1");
}

/// Clone a throwaway "remote" so sync has a real peer over file://.
fn clone_pair(dir: &Path, bin: &Path) -> (std::path::PathBuf, std::path::PathBuf) {
    let srv = dir.join("srv.fossil");
    let st = std::process::Command::new(bin)
        .arg("new")
        .arg(&srv)
        .output()
        .unwrap();
    assert!(st.status.success());
    let loc = dir.join("loc.fossil");
    let st = std::process::Command::new(bin)
        .arg("clone")
        .arg(format!("file://{}", srv.display()))
        .arg(&loc)
        .output()
        .unwrap();
    assert!(st.status.success(), "clone failed");
    (srv, loc)
}

#[tokio::test]
async fn real_sync_to_peer_is_confirmed_and_peer_has_page() {
    let dir = tempfile::tempdir().unwrap();
    let bin = isolated_fossil(dir.path());
    let (srv, loc) = clone_pair(dir.path(), &bin);
    let w = wiki_for(&loc, &bin, dir.path(), true).await;
    let r = w
        .write_wiki_page(wargs(
            "op1",
            "Synced",
            "hello peer",
            Publication::SyncRepository,
        ))
        .await
        .unwrap();
    assert!(!is_error(&r), "{r:?}");
    let rc = parse(&r).receipt.unwrap();
    assert_eq!(
        (rc.commit_state, rc.publication_state),
        (CommitState::Committed, PublicationState::Confirmed)
    );
    let out = std::process::Command::new(&bin)
        .args(["wiki", "export", "Synced", "-R"])
        .arg(&srv)
        .output()
        .unwrap();
    assert!(String::from_utf8_lossy(&out.stdout).contains("hello peer"));
}

#[tokio::test]
async fn real_sync_with_wrong_project_peer_is_not_confirmed() {
    // fossil exits 0 for this case; the receipt must still not say confirmed.
    let dir = tempfile::tempdir().unwrap();
    let bin = isolated_fossil(dir.path());
    let new = |p: &Path| {
        assert!(
            std::process::Command::new(&bin)
                .arg("new")
                .arg(p)
                .output()
                .unwrap()
                .status
                .success()
        )
    };
    let other = dir.path().join("other.fossil");
    let repo = dir.path().join("mine.fossil");
    new(&other);
    new(&repo);
    let url = format!("file://{}", other.display());
    let st = std::process::Command::new(&bin)
        .args(["remote", "add", "peer", &url, "-R"])
        .arg(&repo)
        .output()
        .unwrap();
    assert!(st.status.success());
    let st = std::process::Command::new(&bin)
        .args(["remote", "peer", "-R"])
        .arg(&repo)
        .output()
        .unwrap();
    assert!(st.status.success());
    let w = wiki_for(&repo, &bin, dir.path(), true).await;
    let r = w
        .write_wiki_page(wargs("op1", "P", "v", Publication::SyncRepository))
        .await
        .unwrap();
    let rc = parse(&r).receipt.unwrap();
    assert_eq!(rc.commit_state, CommitState::Committed);
    assert_ne!(rc.publication_state, PublicationState::Confirmed);
    assert!(is_error(&r));
}

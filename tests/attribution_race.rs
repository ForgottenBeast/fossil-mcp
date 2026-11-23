//! Attribution against real Fossil with a competing writer, injected through
//! a wrapper that runs the racer at a chosen point. Same bytes, same page.
mod common;
use common::{parse, real_repo, wargs};
use fossil_mcp::server::types::{ErrorCode, Publication, ReadWikiPageArgs};
use fossil_mcp::{FossilWiki, WikiConfig};
use rmcp::handler::server::wrapper::Parameters;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};

/// Wrapper that, once, runs `fossil wiki commit Race` with the bytes in
/// `racebody` right before the call selected by `trigger` (a shell test).
fn racing_bin(dir: &Path, bin: &Path, repo: &Path, trigger: &str) -> PathBuf {
    let d = dir.display();
    let script = format!(
        "#!/bin/sh\nfor a; do last=\"$a\"; done\nif {trigger} && [ ! -f '{d}/raced' ]; then\n  touch '{d}/raced'\n  '{b}' wiki commit Race -R '{r}' < '{d}/racebody' > /dev/null\nfi\nexec '{b}' \"$@\"\n",
        b = bin.display(),
        r = repo.display()
    );
    let w = dir.join("racing-fossil");
    fs::write(&w, script).unwrap();
    fs::set_permissions(&w, fs::Permissions::from_mode(0o755)).unwrap();
    w
}

fn revisions(bin: &Path, repo: &Path) -> Vec<String> {
    let out = std::process::Command::new(bin)
        .args(["sql", "-R"])
        .arg(repo)
        .arg("SELECT b.uuid FROM tagxref x JOIN tag t ON t.tagid=x.tagid JOIN blob b ON b.rid=x.rid WHERE t.tagname='wiki-Race' ORDER BY x.rid")
        .output()
        .unwrap();
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(|l| l.trim().trim_matches('\'').to_string())
        .collect()
}

async fn wiki(repo: &Path, bin: PathBuf, dir: &Path) -> FossilWiki {
    let mut cfg = WikiConfig::new("itest", repo);
    cfg.fossil_bin = bin;
    cfg.allow_local_writes = true;
    cfg.state_dir = Some(dir.join("state"));
    FossilWiki::bind(cfg).await.unwrap()
}

/// Writer B lands (same bytes, parent A) while our commit C runs: B and C are
/// indistinguishable by content, so B must not be returned.
#[tokio::test]
async fn racer_during_commit_yields_unresolved_never_b() {
    let (repo, bin, dir) = real_repo();
    fs::write(dir.path().join("racebody"), "new").unwrap();
    let w = wiki(&repo, bin.clone(), dir.path()).await;
    let a = parse(
        &w.write_wiki_page(wargs("seed", "Race", "old", Publication::LocalOnly))
            .await
            .unwrap(),
    )
    .receipt
    .unwrap()
    .revision
    .unwrap();
    drop(w);
    let racing = racing_bin(
        dir.path(),
        &bin,
        &repo,
        "[ \"$1\" = wiki ] && [ \"$2\" = commit ]",
    );
    // The wrapper's racer must not recurse into itself: it calls the real bin.
    let w = wiki(&repo, racing, dir.path()).await;
    let r = parse(
        &w.write_wiki_page(wargs("race", "Race", "new", Publication::LocalOnly))
            .await
            .unwrap(),
    );
    let revs = revisions(&bin, &repo);
    assert_eq!(revs.len(), 3, "A, B, C: {revs:?}");
    assert_eq!(revs[0], a);
    let rc = r.receipt.unwrap();
    assert_ne!(
        rc.revision.as_deref(),
        Some(revs[1].as_str()),
        "B returned as ours"
    );
    assert!(
        rc.revision.is_none() || rc.revision.as_deref() == Some(revs[2].as_str()),
        "{rc:?}"
    );
    assert_eq!(rc.error_code, Some(ErrorCode::RevisionUnresolved));
}

/// Writer B lands after our pre-flight read but before our commit starts; the
/// only artifact created by our own commit is C and it must be returned.
#[tokio::test]
async fn racer_before_commit_still_resolves_to_c() {
    let (repo, bin, dir) = real_repo();
    fs::write(dir.path().join("racebody"), "new").unwrap();
    let w = wiki(&repo, bin.clone(), dir.path()).await;
    let _ = w
        .write_wiki_page(wargs("seed", "Race", "old", Publication::LocalOnly))
        .await
        .unwrap();
    drop(w);
    // Fires on the first `fossil sql` call, i.e. after the pre-flight read.
    let racing = racing_bin(dir.path(), &bin, &repo, "[ \"$1\" = sql ]");
    let w = wiki(&repo, racing, dir.path()).await;
    let r = parse(
        &w.write_wiki_page(wargs("race", "Race", "new", Publication::LocalOnly))
            .await
            .unwrap(),
    );
    let revs = revisions(&bin, &repo);
    assert_eq!(revs.len(), 3, "A, B, C: {revs:?}");
    let rc = r.receipt.unwrap();
    assert_eq!(rc.revision.as_deref(), Some(revs[2].as_str()), "{rc:?}");
    let head = w
        .read_wiki_page(Parameters(ReadWikiPageArgs {
            page_name: "Race".into(),
        }))
        .await
        .unwrap()
        .0;
    assert_eq!(head.revision, revs[2]);
}

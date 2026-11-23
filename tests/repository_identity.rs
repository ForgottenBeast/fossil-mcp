//! The journal is bound to the repository, not only to the operator alias.
mod common;
use common::{FakeFossil, bound, is_error, parse, real_repo, wargs};
use fossil_mcp::WikiConfig;
use fossil_mcp::server::types::{
    CommitState, ErrorCode, OperationStatusArgs, Publication, PublicationState,
    ReconcileOperationArgs,
};
use rmcp::handler::server::wrapper::Parameters;

const SYNC: Publication = Publication::SyncRepository;

fn allow_sync(c: &mut WikiConfig) {
    c.allow_repository_sync = true;
}

fn status(op: &str) -> Parameters<OperationStatusArgs> {
    Parameters(OperationStatusArgs {
        operation_id: op.into(),
    })
}

fn retry(op: &str) -> Parameters<ReconcileOperationArgs> {
    Parameters(ReconcileOperationArgs {
        operation_id: op.into(),
        retry_publication: true,
    })
}

/// Write op1 against project PCA, then rebind the same alias and state
/// directory to a different repository (project PCB).
async fn switch_repo(f: &FakeFossil) -> fossil_mcp::FossilWiki {
    std::fs::write(f.file("project_code"), "PCB").unwrap();
    bound(f, allow_sync).await
}

#[tokio::test]
async fn replay_against_a_different_repository_fails_closed() {
    let f = FakeFossil::new();
    std::fs::write(f.file("project_code"), "PCA").unwrap();
    {
        let w = bound(&f, allow_sync).await;
        let r = w
            .write_wiki_page(wargs("op1", "P", "v1", Publication::LocalOnly))
            .await
            .unwrap();
        assert!(!is_error(&r));
    }
    let w = switch_repo(&f).await;
    let r = w
        .write_wiki_page(wargs("op1", "P", "v1", Publication::LocalOnly))
        .await
        .unwrap();
    assert!(is_error(&r));
    assert_eq!(
        parse(&r).error_code,
        Some(ErrorCode::JournalRepositoryMismatch)
    );
    assert_eq!(
        f.calls_to("create").len() + f.calls_to("commit").len(),
        1,
        "neither replayed nor re-written"
    );
    for out in [
        w.wiki_operation_status(status("op1")).await.unwrap(),
        w.wiki_reconcile_operation(retry("op1")).await.unwrap(),
    ] {
        assert_eq!(
            parse(&out).error_code,
            Some(ErrorCode::JournalRepositoryMismatch)
        );
    }
    assert!(f.calls_to("sync").is_empty());
}

#[tokio::test]
async fn pending_receipt_is_not_confirmed_against_another_repository() {
    let f = FakeFossil::new();
    f.on("sync", "echo 'Usage: fossil sync URL' >&2; exit 1");
    std::fs::write(f.file("project_code"), "PCA").unwrap();
    {
        let w = bound(&f, allow_sync).await;
        let r = w
            .write_wiki_page(wargs("op1", "P", "v1", SYNC))
            .await
            .unwrap();
        assert_eq!(
            parse(&r).receipt.unwrap().publication_state,
            PublicationState::Pending
        );
    }
    std::fs::remove_file(f.file("on_sync")).unwrap();
    let w = switch_repo(&f).await;
    let out = w.wiki_reconcile_operation(retry("op1")).await.unwrap();
    assert!(is_error(&out));
    assert_eq!(
        parse(&out).error_code,
        Some(ErrorCode::JournalRepositoryMismatch)
    );
    assert_eq!(
        f.calls_to("sync").len(),
        1,
        "no sync against the wrong repository"
    );
}

#[tokio::test]
async fn missing_artifact_blocks_replay_and_reconcile() {
    let f = FakeFossil::new();
    f.on("sync", "echo 'Usage: fossil sync URL' >&2; exit 1");
    let w = bound(&f, allow_sync).await;
    let r = w
        .write_wiki_page(wargs("op1", "P", "v1", SYNC))
        .await
        .unwrap();
    assert_eq!(
        parse(&r).receipt.unwrap().commit_state,
        CommitState::Committed
    );
    // Same alias, same project, but the repository was restored to a
    // snapshot that never contained the artifact.
    std::fs::write(f.file("missing_artifact"), "").unwrap();
    std::fs::remove_file(f.file("on_sync")).unwrap();
    let out = w.wiki_reconcile_operation(retry("op1")).await.unwrap();
    assert_eq!(
        parse(&out).error_code,
        Some(ErrorCode::JournalRepositoryMismatch)
    );
    assert_ne!(
        parse(&out).receipt.map(|r| r.publication_state),
        Some(PublicationState::Confirmed)
    );
    assert_eq!(f.calls_to("sync").len(), 1, "no new sync");
    let r = w
        .write_wiki_page(wargs("op1", "P", "v1", SYNC))
        .await
        .unwrap();
    assert_eq!(
        parse(&r).error_code,
        Some(ErrorCode::JournalRepositoryMismatch),
        "a stale committed receipt is not replayed"
    );
}

fn plain_reconcile(op: &str) -> Parameters<ReconcileOperationArgs> {
    Parameters(ReconcileOperationArgs {
        operation_id: op.into(),
        retry_publication: false,
    })
}

fn assert_mismatch(out: &rmcp::model::CallToolResult, what: &str) {
    let o = parse(out);
    assert_eq!(
        o.error_code,
        Some(ErrorCode::JournalRepositoryMismatch),
        "{what}"
    );
    assert!(is_error(out), "{what}");
    let committed = o
        .receipt
        .as_ref()
        .is_some_and(|r| r.commit_state == CommitState::Committed);
    assert!(
        !committed,
        "{what}: a missing artifact is never reported committed"
    );
}

#[tokio::test]
async fn status_and_plain_reconcile_check_the_artifact_exists() {
    let f = FakeFossil::new();
    let w = bound(&f, |_| {}).await;
    let r = w
        .write_wiki_page(wargs("op1", "P", "v1", Publication::LocalOnly))
        .await
        .unwrap();
    assert_eq!(
        parse(&r).receipt.unwrap().commit_state,
        CommitState::Committed
    );
    let ok = w.wiki_operation_status(status("op1")).await.unwrap();
    assert!(
        !is_error(&ok) && parse(&ok).receipt.is_some(),
        "present artifact"
    );
    std::fs::write(f.file("missing_artifact"), "").unwrap();
    assert_mismatch(
        &w.wiki_operation_status(status("op1")).await.unwrap(),
        "status",
    );
    assert_mismatch(
        &w.wiki_reconcile_operation(plain_reconcile("op1"))
            .await
            .unwrap(),
        "no-retry reconcile",
    );
}

/// The re-review restore probe with a real repository: same path and project
/// code, restored from a snapshot that predates the write.
#[tokio::test]
async fn restored_repository_is_not_reported_committed_by_status() {
    let (repo, bin, dir) = real_repo();
    let mk = |bin: &std::path::Path| {
        let mut cfg = WikiConfig::new("itest", &repo);
        cfg.fossil_bin = bin.to_path_buf();
        cfg.allow_local_writes = true;
        cfg.state_dir = Some(dir.path().join("state"));
        cfg
    };
    let snapshot = dir.path().join("snapshot.fossil");
    std::fs::copy(&repo, &snapshot).unwrap();
    let w = fossil_mcp::FossilWiki::bind(mk(&bin)).await.unwrap();
    let r = w
        .write_wiki_page(wargs("restore", "Restored", "gone", Publication::LocalOnly))
        .await
        .unwrap();
    assert_eq!(
        parse(&r).receipt.unwrap().commit_state,
        CommitState::Committed
    );
    drop(w);
    std::fs::copy(&snapshot, &repo).unwrap();
    let w = fossil_mcp::FossilWiki::bind(mk(&bin)).await.unwrap();
    assert_mismatch(
        &w.wiki_operation_status(status("restore")).await.unwrap(),
        "status",
    );
    assert_mismatch(
        &w.wiki_reconcile_operation(plain_reconcile("restore"))
            .await
            .unwrap(),
        "no-retry reconcile",
    );
}

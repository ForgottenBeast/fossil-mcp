//! Receipt matrix: every failure/effect boundary through the handler/process seam.
mod common;
use common::{FakeFossil, bound, is_error, parse, wargs};
use fossil_mcp::Limits;
use fossil_mcp::server::types::{
    CommitState, ErrorCode, Publication, PublicationState, RetryAction,
};
use std::time::Duration;

const SYNC: Publication = Publication::SyncRepository;

fn allow_sync(c: &mut fossil_mcp::WikiConfig) {
    c.allow_repository_sync = true;
}

#[tokio::test]
async fn local_only_commit_has_attributed_revision_and_no_sync() {
    let f = FakeFossil::new();
    let w = bound(&f, |_| {}).await;
    let r = w
        .write_wiki_page(wargs("op1", "P", "v1", Publication::LocalOnly))
        .await
        .unwrap();
    assert!(!is_error(&r));
    let rc = parse(&r).receipt.unwrap();
    assert_eq!(rc.commit_state, CommitState::Committed);
    assert_eq!(rc.publication_state, PublicationState::NotRequested);
    assert_eq!(rc.previous_revision, None);
    assert!(rc.revision.as_deref().is_some_and(|r| r.starts_with('u')));
    assert_eq!(rc.error_code, None);
    assert_eq!(rc.retry_action, RetryAction::None);
    assert!(f.calls_to("sync").is_empty(), "local_only must not publish");
}

#[tokio::test]
async fn update_uses_commit_and_chains_previous_revision() {
    let f = FakeFossil::new();
    let w = bound(&f, |_| {}).await;
    let a = parse(
        &w.write_wiki_page(wargs("op1", "P", "v1", Publication::LocalOnly))
            .await
            .unwrap(),
    )
    .receipt
    .unwrap();
    let b = parse(
        &w.write_wiki_page(wargs("op2", "P", "v2", Publication::LocalOnly))
            .await
            .unwrap(),
    )
    .receipt
    .unwrap();
    assert_eq!(f.calls_to("create").len(), 1);
    assert_eq!(f.calls_to("commit").len(), 1);
    assert_eq!(b.previous_revision, a.revision);
    assert_ne!(b.revision, a.revision);
}

#[tokio::test]
async fn sync_success_is_confirmed() {
    let f = FakeFossil::new();
    let w = bound(&f, allow_sync).await;
    let r = w
        .write_wiki_page(wargs("op1", "P", "v1", SYNC))
        .await
        .unwrap();
    assert!(!is_error(&r));
    let rc = parse(&r).receipt.unwrap();
    assert_eq!(
        (rc.commit_state, rc.publication_state),
        (CommitState::Committed, PublicationState::Confirmed)
    );
    assert_eq!(f.calls_to("sync").len(), 1);
}

#[tokio::test]
async fn no_remote_keeps_commit_and_is_pending() {
    let f = FakeFossil::new();
    f.on("sync", "echo 'Usage: fossil sync URL'; exit 1");
    let w = bound(&f, allow_sync).await;
    let r = w
        .write_wiki_page(wargs("op1", "P", "v1", SYNC))
        .await
        .unwrap();
    assert!(is_error(&r), "requested but unpublished is an error result");
    let out = parse(&r);
    let rc = out.receipt.unwrap();
    assert_eq!(rc.commit_state, CommitState::Committed);
    assert!(rc.revision.is_some(), "local outcome is retained");
    assert_eq!(rc.publication_state, PublicationState::Pending);
    assert_eq!(rc.error_code, Some(ErrorCode::NoRemote));
    assert_eq!(rc.retry_action, RetryAction::Reconcile);
    assert_eq!(out.error_code, rc.error_code);
}

#[tokio::test]
async fn sync_failure_never_leaks_child_bytes() {
    let f = FakeFossil::new();
    f.on(
        "sync",
        "echo 'SECRETHOST https://user:TOKEN@x.example/path' >&2; echo 'SECRETOUT'; exit 3",
    );
    let w = bound(&f, allow_sync).await;
    let r = w
        .write_wiki_page(wargs("op1", "P", "v1", SYNC))
        .await
        .unwrap();
    assert!(is_error(&r));
    let wire = serde_json::to_string(&r).unwrap();
    for s in ["SECRET", "TOKEN", "x.example", "/home", "/tmp"] {
        assert!(!wire.contains(s), "leaked {s}: {wire}");
    }
    let rc = parse(&r).receipt.unwrap();
    assert_eq!(rc.commit_state, CommitState::Committed);
    assert_eq!(rc.publication_state, PublicationState::Unknown);
    assert_eq!(rc.error_code, Some(ErrorCode::PublicationUnconfirmed));
}

#[tokio::test]
async fn sync_timeout_is_unknown_not_unpublished() {
    let f = FakeFossil::new();
    f.on("sync", "echo started > \"$D/sync_started\"; exec sleep 30");
    let w = bound(&f, |c| {
        allow_sync(c);
        c.sync_deadline = Duration::from_millis(400);
    })
    .await;
    let r = w
        .write_wiki_page(wargs("op1", "P", "v1", SYNC))
        .await
        .unwrap();
    assert!(f.file("sync_started").exists());
    let rc = parse(&r).receipt.unwrap();
    assert_eq!(
        (rc.commit_state, rc.publication_state),
        (CommitState::Committed, PublicationState::Unknown)
    );
    assert_eq!(rc.retry_action, RetryAction::Reconcile);
    assert!(rc.revision.is_some());
}

#[tokio::test]
async fn commit_timeout_is_unknown_never_not_committed() {
    let f = FakeFossil::new();
    f.on("create", "exec sleep 30");
    let w = bound(&f, |c| {
        allow_sync(c);
        c.limits = Limits {
            deadline: Duration::from_millis(400),
            ..Limits::default()
        };
    })
    .await;
    let r = w
        .write_wiki_page(wargs("op1", "P", "v1", SYNC))
        .await
        .unwrap();
    assert!(is_error(&r));
    let rc = parse(&r).receipt.unwrap();
    assert_eq!(rc.commit_state, CommitState::Unknown);
    assert_eq!(rc.publication_state, PublicationState::Unknown);
    assert_eq!(rc.error_code, Some(ErrorCode::Timeout));
    assert_eq!(rc.retry_action, RetryAction::Reconcile);
    assert!(
        f.calls_to("sync").is_empty(),
        "no publication after an unproven commit"
    );
}

#[tokio::test]
async fn nonzero_commit_exit_is_unknown() {
    let f = FakeFossil::new();
    f.on("create", "echo 'database is locked' >&2; exit 1");
    let w = bound(&f, |_| {}).await;
    let rc = parse(
        &w.write_wiki_page(wargs("op1", "P", "v1", Publication::LocalOnly))
            .await
            .unwrap(),
    )
    .receipt
    .unwrap();
    assert_eq!(rc.commit_state, CommitState::Unknown);
    assert_eq!(rc.retry_action, RetryAction::Reconcile);
}

#[tokio::test]
async fn unattributable_revision_is_unresolved_and_not_published() {
    let f = FakeFossil::new();
    // A "racing writer": head's parent is not the revision we observed.
    f.on("create", "echo foreign > \"$D/force_parent\"");
    let w = bound(&f, allow_sync).await;
    let r = w
        .write_wiki_page(wargs("op1", "P", "v1", SYNC))
        .await
        .unwrap();
    assert!(is_error(&r));
    let rc = parse(&r).receipt.unwrap();
    assert_eq!(rc.commit_state, CommitState::Committed);
    assert_eq!(
        rc.revision, None,
        "never label someone else's revision as ours"
    );
    assert_eq!(rc.error_code, Some(ErrorCode::RevisionUnresolved));
    assert_eq!(rc.retry_action, RetryAction::OperatorRequired);
    assert_eq!(rc.publication_state, PublicationState::Pending);
    assert!(f.calls_to("sync").is_empty(), "no automatic publication");
}

#[tokio::test]
async fn spawn_failure_is_not_committed_and_retryable() {
    let f = FakeFossil::new();
    let w = bound(&f, |_| {}).await;
    std::fs::remove_file(&f.bin).unwrap();
    let r = w
        .write_wiki_page(wargs("op1", "P", "v1", Publication::LocalOnly))
        .await
        .unwrap();
    assert!(is_error(&r));
    let rc = parse(&r).receipt.unwrap();
    assert_eq!(rc.commit_state, CommitState::NotCommitted);
    assert_eq!(rc.error_code, Some(ErrorCode::SpawnFailed));
    assert_eq!(rc.retry_action, RetryAction::RetrySameOperation);
}

#[tokio::test]
async fn write_disabled_and_publication_denied_spawn_nothing() {
    let f = FakeFossil::new();
    let ro = bound(&f, |c| {
        c.allow_local_writes = false;
        c.state_dir = None;
    })
    .await;
    let r = ro
        .write_wiki_page(wargs("op1", "P", "v1", Publication::LocalOnly))
        .await
        .unwrap();
    assert!(is_error(&r));
    assert_eq!(parse(&r).error_code, Some(ErrorCode::WriteDisabled));
    let rw = bound(&f, |_| {}).await;
    let r = rw
        .write_wiki_page(wargs("op2", "P", "v1", SYNC))
        .await
        .unwrap();
    assert_eq!(parse(&r).error_code, Some(ErrorCode::PublicationDenied));
    assert!(f.calls_to("create").is_empty() && f.calls_to("commit").is_empty());
    assert!(
        !f.dir.path().join("state/ops/op2.json").exists(),
        "denied before reserving"
    );
}

/// A concurrent writer adds a sibling with the same parent and makes it the
/// visible head. Parent equality alone cannot tell it from our artifact.
const SIBLING: &str = r#"echo sib > "$D/head_override"
printf 'D t\nL P\nU fx\nW %s\n%s\nZ 00\n' "${SIB_LEN:-4}" "${SIB_BODY:-sibx}" > "$D/artifact_sib"
printf "'sib'\n'u$id'\n" > "$D/sql_out""#;

#[tokio::test]
async fn sibling_with_same_parent_is_never_returned_as_our_revision() {
    let f = FakeFossil::new();
    f.on("create", SIBLING);
    let w = bound(&f, |_| {}).await;
    let r = w
        .write_wiki_page(wargs("op1", "P", "v1", Publication::LocalOnly))
        .await
        .unwrap();
    let rc = parse(&r).receipt.unwrap();
    assert_ne!(
        rc.revision.as_deref(),
        Some("sib"),
        "sibling mislabelled as ours"
    );
    let ours = std::fs::read_to_string(f.file("uuid")).unwrap();
    assert_eq!(
        rc.revision.as_deref(),
        Some(ours.trim()),
        "the artifact whose bytes we wrote is identified"
    );
}

#[tokio::test]
async fn identical_sibling_makes_the_revision_unresolved() {
    let f = FakeFossil::new();
    f.on("create", &format!("SIB_LEN=2; SIB_BODY=v1\n{SIBLING}"));
    let w = bound(&f, |_| {}).await;
    let r = w
        .write_wiki_page(wargs("op1", "P", "v1", Publication::LocalOnly))
        .await
        .unwrap();
    assert!(is_error(&r));
    let rc = parse(&r).receipt.unwrap();
    assert_eq!(rc.revision, None);
    assert_eq!(rc.error_code, Some(ErrorCode::RevisionUnresolved));
    assert_eq!(rc.commit_state, CommitState::Committed);
}

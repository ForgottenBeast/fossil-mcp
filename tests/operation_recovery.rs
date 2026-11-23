//! Idempotency journal: replay, restart windows, reconcile, fail-closed storage.
mod common;
use common::{FakeFossil, bound, is_error, parse, wargs};
use fossil_mcp::server::operations::{
    DEFAULT_JOURNAL_CAP, Journal, Record, RepoIdentity, StoredRequest,
};
use fossil_mcp::server::types::{
    CommitState, ErrorCode, OperationStatusArgs, Publication, PublicationState,
    ReconcileOperationArgs, RetryAction,
};
use fossil_mcp::{Limits, StartupError, WikiConfig};
use rmcp::handler::server::wrapper::Parameters;
use std::time::Duration;

const SYNC: Publication = Publication::SyncRepository;

fn allow_sync(c: &mut WikiConfig) {
    c.allow_repository_sync = true;
}

fn status(op: &str) -> Parameters<OperationStatusArgs> {
    Parameters(OperationStatusArgs {
        operation_id: op.into(),
    })
}

fn reconcile(op: &str, retry: bool) -> Parameters<ReconcileOperationArgs> {
    Parameters(ReconcileOperationArgs {
        operation_id: op.into(),
        retry_publication: retry,
    })
}

#[tokio::test]
async fn same_key_same_request_no_second_commit() {
    let f = FakeFossil::new();
    let w = bound(&f, |_| {}).await;
    let a = w
        .write_wiki_page(wargs("k1", "P", "v1", Publication::LocalOnly))
        .await
        .unwrap();
    let b = w
        .write_wiki_page(wargs("k1", "P", "v1", Publication::LocalOnly))
        .await
        .unwrap();
    assert_eq!(
        f.calls_to("create").len() + f.calls_to("commit").len(),
        1,
        "one effect"
    );
    assert_eq!(
        parse(&a),
        parse(&b),
        "lost reply replays the identical receipt"
    );
}

#[tokio::test]
async fn same_key_changed_request_rejected() {
    let f = FakeFossil::new();
    let w = bound(&f, |_| {}).await;
    w.write_wiki_page(wargs("k1", "P", "v1", Publication::LocalOnly))
        .await
        .unwrap();
    for changed in [
        wargs("k1", "P", "v2", Publication::LocalOnly),
        wargs("k1", "Q", "v1", Publication::LocalOnly),
    ] {
        let r = w.write_wiki_page(changed).await.unwrap();
        assert!(is_error(&r));
        assert_eq!(parse(&r).error_code, Some(ErrorCode::IdempotencyConflict));
    }
    assert_eq!(f.calls_to("create").len() + f.calls_to("commit").len(), 1);
}

#[tokio::test]
async fn simultaneous_same_key_single_effect() {
    let f = FakeFossil::new();
    f.on("create", "echo ready > \"$D/ready\"; sleep 1");
    let w = bound(&f, |_| {}).await;
    let (a, b) = tokio::join!(
        w.write_wiki_page(wargs("k1", "P", "v1", Publication::LocalOnly)),
        async {
            for _ in 0..100 {
                if f.file("ready").exists() {
                    break;
                }
                tokio::time::sleep(Duration::from_millis(20)).await;
            }
            w.write_wiki_page(wargs("k1", "P", "v1", Publication::LocalOnly))
                .await
        }
    );
    let (a, b) = (a.unwrap(), b.unwrap());
    assert_eq!(f.calls_to("create").len(), 1, "exactly one effect");
    assert!(!is_error(&a));
    assert_eq!(
        parse(&b).error_code,
        Some(ErrorCode::Busy),
        "second admission is rejected immediately"
    );
}

#[tokio::test]
async fn restart_after_unknown_never_blindly_commits() {
    let f = FakeFossil::new();
    f.on("create", "exec sleep 30");
    {
        let w = bound(&f, |c| {
            c.limits = Limits {
                deadline: Duration::from_millis(300),
                ..Limits::default()
            }
        })
        .await;
        let r = w
            .write_wiki_page(wargs("k1", "P", "v1", Publication::LocalOnly))
            .await
            .unwrap();
        assert_eq!(
            parse(&r).receipt.unwrap().commit_state,
            CommitState::Unknown
        );
    } // process "restart": lock released
    std::fs::remove_file(f.file("on_create")).unwrap();
    let w = bound(&f, |_| {}).await;
    let r = w
        .write_wiki_page(wargs("k1", "P", "v1", Publication::LocalOnly))
        .await
        .unwrap();
    assert_eq!(
        parse(&r).receipt.unwrap().commit_state,
        CommitState::Unknown,
        "unknown persists across restart"
    );
    assert_eq!(f.calls_to("create").len(), 1, "no second mutation");
    assert_eq!(f.calls_to("commit").len(), 0);
}

#[tokio::test]
async fn restart_after_intent_before_spawn_is_unknown() {
    let f = FakeFossil::new();
    let state = f.dir.path().join("state");
    let ident = RepoIdentity {
        project_code: "PC1".into(),
        path: std::fs::canonicalize(f.repo_file())
            .unwrap()
            .to_string_lossy()
            .into_owned(),
    };
    {
        let j = Journal::open(&state, DEFAULT_JOURNAL_CAP).unwrap();
        let req = StoredRequest {
            page_name: "P".into(),
            content: "v1".into(),
            mimetype: None,
            publication: Publication::LocalOnly,
        };
        j.put("k1", &Record::reservation("repo1", &ident, "k1", req))
            .unwrap();
    } // crash after durable reservation, before any child
    let w = bound(&f, |_| {}).await;
    let r = w
        .write_wiki_page(wargs("k1", "P", "v1", Publication::LocalOnly))
        .await
        .unwrap();
    let rc = parse(&r).receipt.unwrap();
    assert_eq!(rc.commit_state, CommitState::Unknown);
    assert_eq!(rc.retry_action, RetryAction::Reconcile);
    assert!(f.calls_to("create").is_empty() && f.calls_to("commit").is_empty());
}

#[tokio::test]
async fn pre_spawn_failure_can_retry_with_same_key() {
    let f = FakeFossil::new();
    let w = bound(&f, |_| {}).await;
    f.on("get", "exit 3"); // pre-flight read fails: nothing mutating ran
    let r = w
        .write_wiki_page(wargs("k1", "P", "v1", Publication::LocalOnly))
        .await
        .unwrap();
    let rc = parse(&r).receipt.unwrap();
    assert_eq!(
        (rc.commit_state, rc.retry_action),
        (CommitState::NotCommitted, RetryAction::RetrySameOperation)
    );
    std::fs::remove_file(f.file("on_get")).unwrap();
    let r = w
        .write_wiki_page(wargs("k1", "P", "v1", Publication::LocalOnly))
        .await
        .unwrap();
    assert!(!is_error(&r));
    assert_eq!(f.calls_to("create").len(), 1);
}

#[tokio::test]
async fn sync_retry_never_calls_commit() {
    let f = FakeFossil::new();
    f.on("sync", "echo 'Usage: fossil sync URL'; exit 1");
    let w = bound(&f, allow_sync).await;
    let r = w
        .write_wiki_page(wargs("k1", "P", "v1", SYNC))
        .await
        .unwrap();
    let first = parse(&r).receipt.unwrap();
    assert_eq!(first.publication_state, PublicationState::Pending);
    std::fs::remove_file(f.file("on_sync")).unwrap(); // operator fixed the remote
    let r = w
        .wiki_reconcile_operation(reconcile("k1", true))
        .await
        .unwrap();
    assert!(!is_error(&r));
    let rc = parse(&r).receipt.unwrap();
    assert_eq!(rc.publication_state, PublicationState::Confirmed);
    assert_eq!(rc.revision, first.revision, "same receipt identity");
    assert_eq!(
        f.calls_to("create").len() + f.calls_to("commit").len(),
        1,
        "commit never re-run"
    );
    let s = w.wiki_operation_status(status("k1")).await.unwrap();
    assert_eq!(
        parse(&s).receipt.unwrap(),
        rc,
        "status shows the reconciled receipt"
    );
}

#[tokio::test]
async fn reconcile_without_retry_is_read_only_and_ineligible_retry_is_rejected() {
    let f = FakeFossil::new();
    f.on("create", "exit 1");
    let w = bound(&f, allow_sync).await;
    w.write_wiki_page(wargs("k1", "P", "v1", SYNC))
        .await
        .unwrap(); // commit unknown
    let r = w
        .wiki_reconcile_operation(reconcile("k1", false))
        .await
        .unwrap();
    assert_eq!(
        parse(&r).receipt.unwrap().commit_state,
        CommitState::Unknown,
        "unknown preserved"
    );
    let r = w
        .wiki_reconcile_operation(reconcile("k1", true))
        .await
        .unwrap();
    assert!(is_error(&r), "cannot sync-retry an unproven commit");
    assert!(f.calls_to("sync").is_empty());
    let r = w
        .wiki_reconcile_operation(reconcile("nope", false))
        .await
        .unwrap();
    assert_eq!(parse(&r).error_code, Some(ErrorCode::UnknownOperation));
}

#[tokio::test]
async fn wrong_repo_receipt_rejected() {
    let f = FakeFossil::new();
    {
        let w = bound(&f, |_| {}).await;
        w.write_wiki_page(wargs("k1", "P", "v1", Publication::LocalOnly))
            .await
            .unwrap();
    }
    let other = bound(&f, |c| c.repo_id = "repo2".into()).await;
    let s = other.wiki_operation_status(status("k1")).await.unwrap();
    assert_eq!(parse(&s).error_code, Some(ErrorCode::UnknownOperation));
    let w = other
        .write_wiki_page(wargs("k1", "P", "v1", Publication::LocalOnly))
        .await
        .unwrap();
    assert_eq!(parse(&w).error_code, Some(ErrorCode::IdempotencyConflict));
    assert_eq!(f.calls_to("create").len(), 1);
}

#[tokio::test]
async fn corrupt_journal_fails_closed() {
    let f = FakeFossil::new();
    let w = bound(&f, |_| {}).await;
    let ops = f.dir.path().join("state/ops");
    std::fs::write(ops.join("k1.json"), b"{\"version\":1,\"trunc").unwrap();
    let r = w
        .write_wiki_page(wargs("k1", "P", "v1", Publication::LocalOnly))
        .await
        .unwrap();
    assert!(is_error(&r));
    assert_eq!(
        parse(&r).error_code,
        Some(ErrorCode::ReceiptStoreUnavailable)
    );
    std::fs::write(ops.join("k2.json"), br#"{"version":99}"#).unwrap();
    let r = w.wiki_operation_status(status("k2")).await.unwrap();
    assert_eq!(
        parse(&r).error_code,
        Some(ErrorCode::ReceiptStoreUnavailable)
    );
    assert!(f.calls_to("create").is_empty());
}

#[tokio::test]
async fn journal_cap_refuses_writes_instead_of_evicting() {
    let f = FakeFossil::new();
    let w = bound(&f, |c| c.journal_cap = 700).await;
    let big = "x".repeat(2000);
    let r = w
        .write_wiki_page(wargs("k1", "P", &big, Publication::LocalOnly))
        .await
        .unwrap();
    assert_eq!(
        parse(&r).error_code,
        Some(ErrorCode::ReceiptStoreUnavailable)
    );
    assert!(
        f.calls_to("create").is_empty(),
        "refused before any mutation"
    );
}

#[tokio::test]
async fn stale_lock_and_bad_state_dir_fail_startup() {
    let f = FakeFossil::new();
    let state = f.dir.path().join("state");
    std::fs::create_dir_all(&state).unwrap();
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&state, std::fs::Permissions::from_mode(0o700)).unwrap();
    }
    std::fs::write(state.join("LOCK"), "12345").unwrap();
    let mut cfg = WikiConfig::new("repo1", f.repo_file());
    cfg.fossil_bin = f.bin.clone();
    cfg.allow_local_writes = true;
    cfg.state_dir = Some(state.clone());
    assert_eq!(
        fossil_mcp::FossilWiki::bind(cfg.clone())
            .await
            .err()
            .unwrap(),
        StartupError::StateDirUnavailable
    );
    std::fs::remove_file(state.join("LOCK")).unwrap();
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&state, std::fs::Permissions::from_mode(0o755)).unwrap();
    }
    assert_eq!(
        fossil_mcp::FossilWiki::bind(cfg.clone())
            .await
            .err()
            .unwrap(),
        StartupError::StateDirUnavailable,
        "group/world-readable dir"
    );
    cfg.state_dir = None;
    assert_eq!(
        fossil_mcp::FossilWiki::bind(cfg).await.err().unwrap(),
        StartupError::StateDirRequired
    );
}

#[tokio::test]
async fn read_only_startup_does_not_open_the_journal() {
    let f = FakeFossil::new();
    let state = f.dir.path().join("state");
    let w = bound(&f, |c| {
        c.allow_local_writes = false;
    })
    .await;
    assert!(!state.exists(), "no journal directory created");
    let s = w.wiki_operation_status(status("k1")).await.unwrap();
    assert_eq!(parse(&s).error_code, Some(ErrorCode::WriteDisabled));
}

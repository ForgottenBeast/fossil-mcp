//! Property tests for the pure outcome -> receipt mapping.
use fossil_mcp::server::outcome::{
    CommitOutcome, PublishOutcome, ReceiptBase, build_receipt, classify_sync,
};
use fossil_mcp::server::process::{ProcError, ProcOutput};
use fossil_mcp::server::types::{
    CommitState, ErrorCode, Publication, PublicationState, RetryAction,
};
use proptest::prelude::*;

fn code() -> impl Strategy<Value = ErrorCode> {
    prop_oneof![
        Just(ErrorCode::SpawnFailed),
        Just(ErrorCode::Timeout),
        Just(ErrorCode::OutputLimit),
        Just(ErrorCode::CommitUnconfirmed),
        Just(ErrorCode::PublicationUnconfirmed),
        Just(ErrorCode::NoRemote),
    ]
}

fn commit() -> impl Strategy<Value = CommitOutcome> {
    prop_oneof![
        code().prop_map(CommitOutcome::NeverRan),
        code().prop_map(CommitOutcome::Unproven),
        Just(CommitOutcome::Committed { revision: None }),
        "[0-9a-f]{8,64}".prop_map(|r| CommitOutcome::Committed { revision: Some(r) }),
    ]
}

fn publish() -> impl Strategy<Value = Option<PublishOutcome>> {
    prop_oneof![
        Just(None),
        Just(Some(PublishOutcome::Confirmed)),
        code().prop_map(|c| Some(PublishOutcome::Pending(c))),
        code().prop_map(|c| Some(PublishOutcome::Unknown(c))),
    ]
}

fn base() -> ReceiptBase {
    ReceiptBase {
        repo_id: "r".into(),
        operation_id: "o".into(),
        page_name: "P".into(),
        previous_revision: Some("prev".into()),
    }
}

proptest! {
    #[test]
    fn receipt_invariants(c in commit(), p in publish(), sync in any::<bool>()) {
        let req = if sync { Publication::SyncRepository } else { Publication::LocalOnly };
        let r = build_receipt(&base(), req, &c, p.as_ref());
        // confirmed publication implies a confirmed commit with a revision
        if r.publication_state == PublicationState::Confirmed {
            prop_assert_eq!(r.commit_state, CommitState::Committed);
            prop_assert!(r.revision.is_some());
        }
        // uncertainty never becomes not_committed without evidence
        if matches!(c, CommitOutcome::Unproven(_)) {
            prop_assert_eq!(r.commit_state, CommitState::Unknown);
            prop_assert!(r.revision.is_none());
            prop_assert_eq!(r.retry_action, RetryAction::Reconcile);
        }
        // a later sync failure cannot erase a committed commit
        if matches!(c, CommitOutcome::Committed { .. }) {
            prop_assert_eq!(r.commit_state, CommitState::Committed);
        }
        // not_committed only with NeverRan, and then retrying the same op is the action
        if r.commit_state == CommitState::NotCommitted {
            prop_assert!(matches!(c, CommitOutcome::NeverRan(_)));
            prop_assert_eq!(r.retry_action, RetryAction::RetrySameOperation);
        }
        // local_only never reports a publication state other than not_requested
        // except through a failed (never-ran) path, which stays not_requested too
        if !sync {
            prop_assert_eq!(r.publication_state, PublicationState::NotRequested);
        }
        // success implies no error code and no retry
        if r.is_success() {
            prop_assert!(r.error_code.is_none());
            prop_assert_eq!(r.retry_action, RetryAction::None);
        }
        // identity is preserved
        prop_assert_eq!(&r.operation_id, "o");
        prop_assert_eq!(r.previous_revision.as_deref(), Some("prev"));
    }

    /// No arbitrary child bytes survive into the mapped outcome.
    #[test]
    fn classify_sync_is_total_and_sanitized(
        code in proptest::option::of(-2i32..4),
        out in "(?s).{0,300}",
        err in "(?s).{0,300}",
    ) {
        let o = classify_sync(Ok(ProcOutput {
            code, stdout: out.into_bytes(), stderr: err.into_bytes(),
        }));
        // Only fixed enum values are possible; confirmed needs exit 0.
        if o == PublishOutcome::Confirmed {
            prop_assert_eq!(code, Some(0));
        }
    }

    #[test]
    fn proc_errors_map_to_non_confirmed(e in prop_oneof![
        Just(ProcError::Spawn), Just(ProcError::Timeout),
        Just(ProcError::OutputLimit), Just(ProcError::Io)]) {
        prop_assert_ne!(classify_sync(Err(e)), PublishOutcome::Confirmed);
    }
}

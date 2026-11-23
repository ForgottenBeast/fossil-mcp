//! Pure mapping from observed effects to a [`WriteReceipt`].
//!
//! No I/O lives here, so the invariants (a confirmed publication implies a
//! confirmed commit; uncertainty never becomes `not_committed`; codes are
//! fixed) are property-testable without spawning anything.

use crate::server::process::{ProcError, ProcOutput};
use crate::server::types::{
    CommitState, ErrorCode, Publication, PublicationState, RECEIPT_VERSION, RetryAction,
    WriteReceipt,
};

/// What is known about the local commit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CommitOutcome {
    /// Nothing that could mutate ran (pre-flight failure or spawn failure).
    NeverRan(ErrorCode),
    /// A mutating child started but its effect cannot be proven either way.
    Unproven(ErrorCode),
    /// The child reported completion; `revision` is set only if attributed.
    Committed {
        /// Attributed artifact id, if established.
        revision: Option<String>,
    },
}

/// What is known about publication (only meaningful after a commit).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PublishOutcome {
    /// `fossil sync` completed against a peer.
    Confirmed,
    /// Provably not performed.
    Pending(ErrorCode),
    /// May have been performed.
    Unknown(ErrorCode),
}

/// Identity fields shared by every receipt of one operation.
#[derive(Debug, Clone)]
pub struct ReceiptBase {
    /// Bound repository alias.
    pub repo_id: String,
    /// Idempotency key.
    pub operation_id: String,
    /// Target page.
    pub page_name: String,
    /// Head observed before writing.
    pub previous_revision: Option<String>,
}

/// Combine the stage outcomes into a receipt.
///
/// `publish` is consulted only when the commit completed with an attributed
/// revision and publication was requested.
pub fn build_receipt(
    base: &ReceiptBase,
    requested: Publication,
    commit: &CommitOutcome,
    publish: Option<&PublishOutcome>,
) -> WriteReceipt {
    let wants = requested == Publication::SyncRepository;
    let mut r = WriteReceipt {
        receipt_version: RECEIPT_VERSION,
        repo_id: base.repo_id.clone(),
        operation_id: base.operation_id.clone(),
        page_name: base.page_name.clone(),
        previous_revision: base.previous_revision.clone(),
        revision: None,
        commit_state: CommitState::NotCommitted,
        publication_state: PublicationState::NotRequested,
        error_code: None,
        retry_action: RetryAction::None,
    };
    match commit {
        CommitOutcome::NeverRan(code) => {
            r.publication_state = if wants {
                PublicationState::Pending
            } else {
                PublicationState::NotRequested
            };
            r.error_code = Some(*code);
            r.retry_action = RetryAction::RetrySameOperation;
        }
        CommitOutcome::Unproven(code) => {
            r.commit_state = CommitState::Unknown;
            r.publication_state = if wants {
                PublicationState::Unknown
            } else {
                PublicationState::NotRequested
            };
            r.error_code = Some(*code);
            r.retry_action = RetryAction::Reconcile;
        }
        CommitOutcome::Committed { revision: None } => {
            r.commit_state = CommitState::Committed;
            r.publication_state = if wants {
                PublicationState::Pending
            } else {
                PublicationState::NotRequested
            };
            r.error_code = Some(ErrorCode::RevisionUnresolved);
            r.retry_action = RetryAction::OperatorRequired;
        }
        CommitOutcome::Committed {
            revision: Some(rev),
        } => {
            r.commit_state = CommitState::Committed;
            r.revision = Some(rev.clone());
            if !wants {
                return r;
            }
            match publish {
                Some(PublishOutcome::Confirmed) => {
                    r.publication_state = PublicationState::Confirmed
                }
                Some(PublishOutcome::Pending(code)) => {
                    r.publication_state = PublicationState::Pending;
                    r.error_code = Some(*code);
                    r.retry_action = RetryAction::Reconcile;
                }
                Some(PublishOutcome::Unknown(code)) => {
                    r.publication_state = PublicationState::Unknown;
                    r.error_code = Some(*code);
                    r.retry_action = RetryAction::Reconcile;
                }
                None => {
                    r.publication_state = PublicationState::Pending;
                    r.error_code = Some(ErrorCode::PublicationUnconfirmed);
                    r.retry_action = RetryAction::Reconcile;
                }
            }
        }
    }
    r
}

/// Map a failed child run to an error code (never embeds child bytes).
pub fn proc_error_code(e: ProcError) -> ErrorCode {
    match e {
        ProcError::Spawn => ErrorCode::SpawnFailed,
        ProcError::Timeout => ErrorCode::Timeout,
        ProcError::OutputLimit => ErrorCode::OutputLimit,
        ProcError::Io => ErrorCode::CommitUnconfirmed,
    }
}

/// Classify a finished `fossil sync` run.
///
/// Fossil exits 0 even when the peer is unreachable or the project differs,
/// so success needs a positive round-trip count and no `Error` line.
pub fn classify_sync(run: Result<ProcOutput, ProcError>) -> PublishOutcome {
    let out = match run {
        Ok(o) => o,
        Err(ProcError::Spawn) => return PublishOutcome::Pending(ErrorCode::SpawnFailed),
        Err(_) => return PublishOutcome::Unknown(ErrorCode::PublicationUnconfirmed),
    };
    let text = format!(
        "{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    if out.code == Some(1) && (text.contains("Usage:") && text.contains(" sync URL")) {
        return PublishOutcome::Pending(ErrorCode::NoRemote);
    }
    if out.code != Some(0) {
        return PublishOutcome::Unknown(ErrorCode::PublicationUnconfirmed);
    }
    let has_error_line = text.lines().any(|l| {
        let l = l.trim_start().to_ascii_lowercase();
        l.starts_with("error") || l.starts_with("ssl:") || l.contains("cannot connect")
    });
    match round_trips(&text) {
        Some(n) if n >= 1 && !has_error_line => PublishOutcome::Confirmed,
        Some(0) => PublishOutcome::Pending(ErrorCode::PublicationUnconfirmed),
        _ => PublishOutcome::Unknown(ErrorCode::PublicationUnconfirmed),
    }
}

fn round_trips(text: &str) -> Option<u64> {
    let rest = text.split("Round-trips:").nth(1)?;
    rest.split_whitespace().next()?.parse().ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn base() -> ReceiptBase {
        ReceiptBase {
            repo_id: "r".into(),
            operation_id: "o".into(),
            page_name: "P".into(),
            previous_revision: None,
        }
    }

    fn out(code: i32, s: &str) -> Result<ProcOutput, ProcError> {
        Ok(ProcOutput {
            code: Some(code),
            stdout: s.as_bytes().to_vec(),
            stderr: vec![],
        })
    }

    #[test]
    fn sync_rc0_with_error_line_is_not_confirmed() {
        let o = classify_sync(out(
            0,
            "Error: wrong project\nRound-trips: 1   Artifacts sent: 0",
        ));
        assert_eq!(
            o,
            PublishOutcome::Unknown(ErrorCode::PublicationUnconfirmed)
        );
    }

    #[test]
    fn sync_rc0_zero_round_trips_is_pending() {
        let o = classify_sync(out(
            0,
            "SSL: cannot open socket\nRound-trips: 0   Artifacts sent: 0",
        ));
        assert_eq!(
            o,
            PublishOutcome::Pending(ErrorCode::PublicationUnconfirmed)
        );
    }

    #[test]
    fn sync_usage_error_means_no_remote() {
        assert_eq!(
            classify_sync(out(1, "Usage: fossil sync URL")),
            PublishOutcome::Pending(ErrorCode::NoRemote)
        );
    }

    #[test]
    fn sync_clean_run_is_confirmed() {
        assert_eq!(
            classify_sync(out(
                0,
                "Round-trips: 2   Artifacts sent: 1  received: 0\nSync done"
            )),
            PublishOutcome::Confirmed
        );
    }

    #[test]
    fn timeout_after_commit_is_unknown_publication_not_failed_commit() {
        let r = build_receipt(
            &base(),
            Publication::SyncRepository,
            &CommitOutcome::Committed {
                revision: Some("abc".into()),
            },
            Some(&PublishOutcome::Unknown(ErrorCode::PublicationUnconfirmed)),
        );
        assert_eq!(r.commit_state, CommitState::Committed);
        assert_eq!(r.publication_state, PublicationState::Unknown);
        assert_eq!(r.revision.as_deref(), Some("abc"));
        assert_eq!(r.retry_action, RetryAction::Reconcile);
        assert!(!r.is_success());
    }
}

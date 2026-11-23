//! Wire types for the MCP tools.
//!
//! These Rust/Serde/Schemars types are the single authority for tool schemas.
//! No model-facing field carries a credential, session token or path: the
//! repository is bound once at process start (see [`crate::server::binding`]).

use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

/// Longest accepted page name in UTF-8 bytes.
pub const MAX_PAGE_NAME_BYTES: usize = 256;
/// Longest accepted page content in UTF-8 bytes.
pub const MAX_CONTENT_BYTES: usize = 1 << 20;
/// Longest accepted operation id in bytes.
pub const MAX_OPERATION_ID_BYTES: usize = 64;

/// Arguments for the `read_wiki_page` tool.
#[derive(Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct ReadWikiPageArgs {
    /// Name of the wiki page to read.
    pub page_name: String,
}

/// Response of `list_wiki_pages`.
#[derive(Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
pub struct ListWikiPagesResponse {
    /// Page names in the bound repository.
    pub pages: Vec<String>,
}

/// Response of `read_wiki_page`.
#[derive(Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
pub struct ReadWikiPageResponse {
    /// Name of the page that was read.
    pub page_name: String,
    /// Exact page content.
    pub content: String,
    /// Fossil artifact id of the version read (a CAS token for a future
    /// authoritative write gate; not enforced by this server).
    pub revision: String,
}

/// Allowed page MIME types.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
pub enum WikiMimetype {
    /// `text/x-fossil-wiki`
    #[serde(rename = "text/x-fossil-wiki")]
    FossilWiki,
    /// `text/x-markdown`
    #[serde(rename = "text/x-markdown")]
    Markdown,
    /// `text/plain`
    #[serde(rename = "text/plain")]
    Plain,
}

impl WikiMimetype {
    /// The value passed to `fossil wiki --mimetype`.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::FossilWiki => "text/x-fossil-wiki",
            Self::Markdown => "text/x-markdown",
            Self::Plain => "text/plain",
        }
    }
}

/// How far a write is published.
#[derive(Debug, Clone, Copy, Default, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Publication {
    /// Commit to the bound repository only (default).
    #[default]
    LocalOnly,
    /// Also run `fossil sync`, which may publish **all** sharable repository
    /// artifacts, not just this page. Requires startup opt-in.
    SyncRepository,
}

/// Arguments for the `write_wiki_page` tool.
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct WriteWikiPageArgs {
    /// Caller-generated idempotency key: 1-64 ASCII letters, digits, `_` or `-`.
    pub operation_id: String,
    /// Page name: non-empty, at most 256 bytes, no NUL, not starting with `-`.
    pub page_name: String,
    /// Page content (at most 1 MiB).
    pub content: String,
    /// Optional MIME type; defaults to the page's previous type.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub mimetype: Option<WikiMimetype>,
    /// Publication mode; defaults to `local_only`.
    #[serde(default)]
    pub publication: Publication,
}

/// Arguments for `wiki_operation_status`.
#[derive(Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct OperationStatusArgs {
    /// Operation id of an earlier write.
    pub operation_id: String,
}

/// Arguments for `wiki_reconcile_operation`.
#[derive(Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct ReconcileOperationArgs {
    /// Operation id of an earlier write.
    pub operation_id: String,
    /// When true, retry only the sync of an already committed revision.
    /// Never creates a wiki artifact.
    #[serde(default)]
    pub retry_publication: bool,
}

/// Whether the local Fossil commit happened.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum CommitState {
    /// Provably no commit was made.
    NotCommitted,
    /// The commit completed locally.
    Committed,
    /// A commit may or may not have happened.
    Unknown,
}

/// Whether the committed change reached the configured peer.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum PublicationState {
    /// Publication was not requested.
    NotRequested,
    /// Requested but provably not yet performed.
    Pending,
    /// `fossil sync` completed against the configured peer. Does not prove
    /// this revision is the winner visible on the remote.
    Confirmed,
    /// A publication may or may not have happened.
    Unknown,
}

/// What the caller may do next.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum RetryAction {
    /// Nothing to do.
    None,
    /// Calling `write_wiki_page` again with the same operation id is safe.
    RetrySameOperation,
    /// Use `wiki_reconcile_operation`; never re-commit.
    Reconcile,
    /// An operator must inspect the repository.
    OperatorRequired,
}

/// Fixed, sanitized error codes. Messages never contain child output, paths,
/// URLs, content or credentials.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ErrorCode {
    /// Write/reconcile attempted without `--allow-local-writes`.
    WriteDisabled,
    /// `sync_repository` requested without `--allow-repository-sync`.
    PublicationDenied,
    /// Arguments failed validation.
    InvalidArgument,
    /// Another mutation is in flight (or admission is saturated).
    Busy,
    /// The `fossil` executable could not be started.
    SpawnFailed,
    /// The child exceeded its deadline.
    Timeout,
    /// The child exceeded an output cap.
    OutputLimit,
    /// The child failed in a way that does not prove it left no effect.
    CommitUnconfirmed,
    /// The page does not exist.
    PageNotFound,
    /// Reading the page failed before any mutation.
    PreflightFailed,
    /// No remote URL is configured for sync.
    NoRemote,
    /// Sync ran but its outcome is not confirmed.
    PublicationUnconfirmed,
    /// The commit completed but its artifact id cannot be attributed to it.
    RevisionUnresolved,
    /// The operation id was used with a different request.
    IdempotencyConflict,
    /// The operation id is unknown.
    UnknownOperation,
    /// The receipt journal is unavailable, corrupt or full.
    ReceiptStoreUnavailable,
    /// The response from fossil could not be understood or was too large.
    BadResponse,
    /// The journal record belongs to a different repository than the bound
    /// one (project code or path differs, or its artifact is absent).
    JournalRepositoryMismatch,
    /// The sidecar rejected the credential (after one refresh) or the issuer
    /// refused the grant: key, allowlist or audience need operator action.
    BacklinksAuthFailed,
    /// The sidecar or the issuer could not be reached.
    BacklinksUnreachable,
    /// The credential file is unreadable, unsafe or invalid.
    CredentialUnavailable,
}

impl ErrorCode {
    /// Fixed human-readable message for this code.
    pub fn message(self) -> &'static str {
        match self {
            Self::WriteDisabled => "writes are disabled for this server instance",
            Self::PublicationDenied => "repository sync is not permitted for this server instance",
            Self::InvalidArgument => "invalid argument",
            Self::Busy => "another operation is in progress",
            Self::SpawnFailed => "the fossil executable could not be started",
            Self::Timeout => "the fossil command timed out",
            Self::OutputLimit => "the fossil command produced too much output",
            Self::CommitUnconfirmed => "the commit outcome is not confirmed",
            Self::PageNotFound => "wiki page not found",
            Self::PreflightFailed => "reading the current page failed",
            Self::NoRemote => "no remote is configured for sync",
            Self::PublicationUnconfirmed => "publication is not confirmed",
            Self::RevisionUnresolved => "the committed revision could not be attributed",
            Self::IdempotencyConflict => "operation id was already used with a different request",
            Self::UnknownOperation => "unknown operation id",
            Self::ReceiptStoreUnavailable => "the receipt store is unavailable",
            Self::BadResponse => "unexpected response from fossil",
            Self::JournalRepositoryMismatch => {
                "the receipt journal belongs to a different repository state"
            }
            Self::BacklinksAuthFailed => "the backlinks service rejected the credential",
            Self::BacklinksUnreachable => "the backlinks service could not be reached",
            Self::CredentialUnavailable => "the backlinks credential is unavailable",
        }
    }
}

/// Receipt schema version.
pub const RECEIPT_VERSION: u32 = 1;

/// Typed outcome of a write. The shape is the plug-in point for a future
/// remote authority / compare-and-swap gate: `previous_revision` is the
/// precondition observed, `revision` the artifact it produced.
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
pub struct WriteReceipt {
    /// Always [`RECEIPT_VERSION`].
    pub receipt_version: u32,
    /// Alias of the bound repository.
    pub repo_id: String,
    /// Caller-supplied idempotency key.
    pub operation_id: String,
    /// Page the operation targeted.
    pub page_name: String,
    /// Artifact id of the page head observed before writing (null for a new page).
    pub previous_revision: Option<String>,
    /// Artifact id of the committed version (null unless attributed).
    pub revision: Option<String>,
    /// Local commit state.
    pub commit_state: CommitState,
    /// Publication state.
    pub publication_state: PublicationState,
    /// Fixed error code when the outcome is not fully successful.
    pub error_code: Option<ErrorCode>,
    /// Next action.
    pub retry_action: RetryAction,
}

impl WriteReceipt {
    /// True when the operation is fully successful for its requested mode.
    pub fn is_success(&self) -> bool {
        self.error_code.is_none()
            && self.commit_state == CommitState::Committed
            && matches!(
                self.publication_state,
                PublicationState::NotRequested | PublicationState::Confirmed
            )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn write_args_reject_retired_and_unknown_fields() {
        for field in [
            "force_write",
            "skip_sync",
            "password",
            "api_key",
            "repo_path",
        ] {
            let j = format!(
                r#"{{"operation_id":"o","page_name":"P","content":"c","{field}":"SENTINEL"}}"#
            );
            let err = serde_json::from_str::<WriteWikiPageArgs>(&j)
                .unwrap_err()
                .to_string();
            assert!(
                !err.contains("SENTINEL"),
                "error must not echo values: {err}"
            );
        }
    }

    #[test]
    fn write_args_defaults() {
        let a: WriteWikiPageArgs =
            serde_json::from_str(r#"{"operation_id":"o","page_name":"P","content":"c"}"#).unwrap();
        assert_eq!(a.publication, Publication::LocalOnly);
        assert_eq!(a.mimetype, None);
    }

    #[test]
    fn mimetype_is_an_allowlist() {
        assert!(serde_json::from_str::<WikiMimetype>(r#""text/html""#).is_err());
        assert_eq!(
            serde_json::from_str::<WikiMimetype>(r#""text/x-markdown""#).unwrap(),
            WikiMimetype::Markdown
        );
    }

    #[test]
    fn receipt_nullable_fields_serialize_as_null() {
        let r = WriteReceipt {
            receipt_version: RECEIPT_VERSION,
            repo_id: "r".into(),
            operation_id: "o".into(),
            page_name: "P".into(),
            previous_revision: None,
            revision: None,
            commit_state: CommitState::NotCommitted,
            publication_state: PublicationState::NotRequested,
            error_code: None,
            retry_action: RetryAction::None,
        };
        let v = serde_json::to_value(&r).unwrap();
        assert!(v["previous_revision"].is_null());
        assert!(v["revision"].is_null());
        assert!(v["error_code"].is_null());
        assert_eq!(v["commit_state"], "not_committed");
    }

    #[test]
    fn error_codes_serialize_snake_case_with_fixed_messages() {
        let v = serde_json::to_value(ErrorCode::PublicationUnconfirmed).unwrap();
        assert_eq!(v, "publication_unconfirmed");
        assert!(!ErrorCode::Busy.message().is_empty());
    }
}

//! MCP server implementation for Fossil SCM wiki operations.
//!
//! [`FossilWiki`] is bound to exactly one repository at construction
//! ([`FossilWiki::bind`]); nothing a client sends can change that binding.
//! The stable tool catalog is `list_wiki_pages`, `read_wiki_page`,
//! `write_wiki_page`, `wiki_operation_status` and `wiki_reconcile_operation`.
//! Writes and reconciliation are disabled unless the operator opts in.
//!
//! Every `fossil` child runs under the bounded runner in [`process`]; page
//! bytes travel over stdin and no temporary content file exists. Failures
//! surface as fixed [`types::ErrorCode`]s, never raw child output.
//!
//! ```rust,no_run
//! use fossil_mcp::{FossilWiki, WikiConfig};
//!
//! # async fn example() -> Result<(), Box<dyn std::error::Error>> {
//! let wiki = FossilWiki::bind(WikiConfig::new("notes", "/path/to/repo.fossil")).await?;
//! // Hand `wiki` to rmcp's `ServiceExt::serve` with a stdio transport.
//! # let _ = wiki;
//! # Ok(())
//! # }
//! ```

use rmcp::{
    ErrorData, Json,
    handler::server::{ServerHandler, tool::ToolRouter, wrapper::Parameters},
    model::{CallToolResult, ServerCapabilities, ServerInfo},
    tool, tool_router,
};
use serde::{Deserialize, Serialize};
use std::ffi::OsString;
use std::path::PathBuf;
use std::sync::Arc;
use tokio::sync::{Mutex, Semaphore};

pub mod binding;
pub mod operations;
pub mod outcome;
pub mod process;
pub mod types;

use binding::{RepositoryBinding, StartupError, WikiConfig};
use operations::{Journal, JournalError, Record, StoredRequest, valid_operation_id};
use outcome::{
    CommitOutcome, PublishOutcome, ReceiptBase, build_receipt, classify_sync, proc_error_code,
};
use process::{Limits, ProcError, ProcOutput};
use types::{
    ErrorCode, MAX_CONTENT_BYTES, MAX_PAGE_NAME_BYTES, OperationStatusArgs, Publication,
    ReadWikiPageArgs, ReconcileOperationArgs, WriteReceipt, WriteWikiPageArgs,
};

/// Maximum concurrently running `fossil` children.
const MAX_ACTIVE_CHILDREN: usize = 4;

/// Parses the output of `fossil wiki list` into a vector of page names.
///
/// Filters out empty lines and trims whitespace from each page name.
///
/// ```
/// use fossil_mcp::server::parse_wiki_list;
///
/// let output = "HomePage\n  About  \n\nDocs/API\n";
/// assert_eq!(parse_wiki_list(output), vec!["HomePage", "About", "Docs/API"]);
/// ```
pub fn parse_wiki_list(output: &str) -> Vec<String> {
    output
        .lines()
        .map(|line| line.trim().to_string())
        .filter(|line| !line.is_empty())
        .collect()
}

/// Whether `name` is an acceptable wiki page name: non-empty, at most 256
/// bytes, no NUL/CR/LF, and not option-like (leading `-`).
pub fn valid_page_name(name: &str) -> bool {
    !name.is_empty()
        && name.len() <= MAX_PAGE_NAME_BYTES
        && !name.starts_with('-')
        && !name.bytes().any(|b| b == 0 || b == b'\n' || b == b'\r')
}

/// Validate a write request into the bytes retained for replay.
pub fn validate_write(args: &WriteWikiPageArgs) -> Result<StoredRequest, ErrorCode> {
    if !valid_operation_id(&args.operation_id)
        || !valid_page_name(&args.page_name)
        || args.content.len() > MAX_CONTENT_BYTES
    {
        return Err(ErrorCode::InvalidArgument);
    }
    Ok(StoredRequest {
        page_name: args.page_name.clone(),
        content: args.content.clone(),
        mimetype: args.mimetype,
        publication: args.publication,
    })
}

/// Structured output of the write-family tools. `receipt` is present
/// whenever an operation identity exists, even for errors.
#[derive(Debug, Clone, Serialize, Deserialize, schemars::JsonSchema, PartialEq, Eq)]
pub struct WriteToolOutput {
    /// The operation receipt, when one exists.
    pub receipt: Option<WriteReceipt>,
    /// Fixed error code when the result is an error.
    pub error_code: Option<ErrorCode>,
    /// Fixed message for the code.
    pub message: Option<String>,
}

enum Head {
    Absent,
    Present {
        uuid: String,
        parent: Option<String>,
        content: String,
    },
}

#[derive(Deserialize)]
struct JsonWiki {
    #[serde(rename = "resultCode")]
    result_code: Option<String>,
    payload: Option<JsonPayload>,
}

#[derive(Deserialize)]
struct JsonPayload {
    uuid: String,
    parent: Option<String>,
    content: Option<String>,
}

struct Inner {
    binding: RepositoryBinding,
    fossil_bin: PathBuf,
    limits: Limits,
    sync_limits: Limits,
    allow_local_writes: bool,
    allow_repository_sync: bool,
    journal: Option<Journal>,
    mutation: Mutex<()>,
    children: Semaphore,
}

/// MCP handler for one bound Fossil repository.
///
/// Cloning shares the same immutable binding, journal and admission guards.
#[derive(Clone)]
pub struct FossilWiki {
    inner: Arc<Inner>,
    tool_router: ToolRouter<Self>,
}

fn fail(code: ErrorCode) -> Result<CallToolResult, ErrorData> {
    let out = WriteToolOutput {
        receipt: None,
        error_code: Some(code),
        message: Some(code.message().into()),
    };
    Ok(CallToolResult::structured_error(
        serde_json::to_value(out).expect("serializable"),
    ))
}

fn receipt_result(receipt: WriteReceipt, as_error: bool) -> Result<CallToolResult, ErrorData> {
    let out = WriteToolOutput {
        error_code: receipt.error_code,
        message: receipt.error_code.map(|c| c.message().to_string()),
        receipt: Some(receipt),
    };
    let v = serde_json::to_value(out).expect("serializable");
    Ok(if as_error {
        CallToolResult::structured_error(v)
    } else {
        CallToolResult::structured(v)
    })
}

fn text_error(code: ErrorCode) -> String {
    let name = serde_json::to_value(code)
        .ok()
        .and_then(|v| v.as_str().map(String::from));
    format!("{}: {}", name.unwrap_or_default(), code.message())
}

impl FossilWiki {
    /// Validate the configuration and bind to the repository.
    ///
    /// Fails (before any MCP service starts) unless the repository is a
    /// regular non-empty non-symlink file that `fossil` accepts, and, when
    /// writes are enabled, the receipt journal can be opened and locked.
    pub async fn bind(cfg: WikiConfig) -> Result<Self, StartupError> {
        let binding = RepositoryBinding::check(&cfg)?;
        let journal = if cfg.allow_local_writes {
            let dir = cfg
                .state_dir
                .as_ref()
                .ok_or(StartupError::StateDirRequired)?;
            Some(
                Journal::open(dir, cfg.journal_cap)
                    .map_err(|_| StartupError::StateDirUnavailable)?,
            )
        } else {
            None
        };
        let mut sync_limits = cfg.limits;
        sync_limits.deadline = cfg.sync_deadline;
        let wiki = Self {
            inner: Arc::new(Inner {
                binding,
                fossil_bin: cfg.fossil_bin,
                limits: cfg.limits,
                sync_limits,
                allow_local_writes: cfg.allow_local_writes,
                allow_repository_sync: cfg.allow_repository_sync,
                journal,
                mutation: Mutex::new(()),
                children: Semaphore::new(MAX_ACTIVE_CHILDREN),
            }),
            tool_router: Self::tool_router(),
        };
        match wiki
            .run(
                &["wiki", "list", "-R", &wiki.repo_arg()],
                None,
                wiki.inner.limits,
            )
            .await
        {
            Ok(o) if o.success() => Ok(wiki),
            Err(ProcError::Spawn) => Err(StartupError::FossilUnavailable),
            _ => Err(StartupError::NotAFossilRepository),
        }
    }

    /// Alias of the bound repository.
    pub fn repo_id(&self) -> &str {
        self.inner.binding.repo_id()
    }

    fn repo_arg(&self) -> String {
        self.inner.binding.path.to_string_lossy().into_owned()
    }

    async fn run(
        &self,
        args: &[&str],
        stdin: Option<&[u8]>,
        limits: Limits,
    ) -> Result<ProcOutput, ProcError> {
        let _permit = self
            .inner
            .children
            .try_acquire()
            .map_err(|_| ProcError::Io)?;
        let args: Vec<OsString> = args.iter().map(Into::into).collect();
        process::run(&self.inner.fossil_bin, &args, stdin, &limits).await
    }

    /// Read the current head of `page` via `fossil json wiki get`.
    async fn head(&self, page: &str) -> Result<Head, ErrorCode> {
        let mut limits = self.inner.limits;
        limits.stdout_max = limits.stdout_max.saturating_mul(4);
        let out = self
            .run(
                &[
                    "json",
                    "wiki",
                    "get",
                    "--name",
                    page,
                    "-R",
                    &self.repo_arg(),
                ],
                None,
                limits,
            )
            .await
            .map_err(|e| match e {
                ProcError::Spawn => ErrorCode::SpawnFailed,
                ProcError::Timeout => ErrorCode::Timeout,
                ProcError::OutputLimit => ErrorCode::OutputLimit,
                ProcError::Io => ErrorCode::PreflightFailed,
            })?;
        if !out.success() {
            return Err(ErrorCode::PreflightFailed);
        }
        let parsed: JsonWiki =
            serde_json::from_slice(&out.stdout).map_err(|_| ErrorCode::BadResponse)?;
        match (parsed.result_code.as_deref(), parsed.payload) {
            (Some("FOSSIL-3006"), _) => Ok(Head::Absent),
            (None, Some(p)) => Ok(Head::Present {
                uuid: p.uuid,
                parent: p.parent.filter(|s| !s.is_empty()),
                content: p.content.unwrap_or_default(),
            }),
            _ => Err(ErrorCode::BadResponse),
        }
    }

    fn journal(&self) -> Result<&Journal, ErrorCode> {
        if !self.inner.allow_local_writes {
            return Err(ErrorCode::WriteDisabled);
        }
        self.inner
            .journal
            .as_ref()
            .ok_or(ErrorCode::ReceiptStoreUnavailable)
    }

    fn persist(&self, id: &str, rec: &Record) -> Result<(), ErrorCode> {
        self.journal()?
            .put(id, rec)
            .map_err(|_| ErrorCode::ReceiptStoreUnavailable)
    }

    async fn sync(&self) -> PublishOutcome {
        let repo = self.repo_arg();
        classify_sync(
            self.run(&["sync", "-R", &repo], None, self.inner.sync_limits)
                .await,
        )
    }

    /// Execute one reserved write; persists each stage.
    async fn execute(&self, id: &str, mut rec: Record) -> Result<WriteReceipt, ErrorCode> {
        let req = rec.request.clone();
        let mut base = ReceiptBase {
            repo_id: self.repo_id().to_string(),
            operation_id: id.to_string(),
            page_name: req.page_name.clone(),
            previous_revision: None,
        };
        let finish = |this: &Self,
                      rec: &mut Record,
                      base: &ReceiptBase,
                      c: CommitOutcome,
                      p: Option<&PublishOutcome>| {
            rec.receipt = build_receipt(base, req.publication, &c, p);
            this.persist(id, rec).map(|_| rec.receipt.clone())
        };

        // Read-only pre-flight: observe the head so create/commit is chosen
        // from data, not from English error text.
        let head = match self.head(&req.page_name).await {
            Ok(h) => h,
            Err(code) => {
                let code = if code == ErrorCode::Timeout
                    || code == ErrorCode::OutputLimit
                    || code == ErrorCode::SpawnFailed
                {
                    code
                } else {
                    ErrorCode::PreflightFailed
                };
                return finish(self, &mut rec, &base, CommitOutcome::NeverRan(code), None);
            }
        };
        let (sub, prev) = match &head {
            Head::Absent => ("create", None),
            Head::Present { uuid, .. } => ("commit", Some(uuid.clone())),
        };
        base.previous_revision = prev.clone();

        let repo = self.repo_arg();
        let mimetype = req.mimetype.map(|m| format!("--mimetype={}", m.as_str()));
        let mut argv = vec!["wiki", sub, req.page_name.as_str(), "-R", repo.as_str()];
        if let Some(m) = &mimetype {
            argv.push(m);
        }
        let ran = self
            .run(&argv, Some(req.content.as_bytes()), self.inner.limits)
            .await;
        let commit = match ran {
            Err(ProcError::Spawn) => CommitOutcome::NeverRan(ErrorCode::SpawnFailed),
            Err(e) => CommitOutcome::Unproven(proc_error_code(e)),
            Ok(o) if !o.success() => CommitOutcome::Unproven(ErrorCode::CommitUnconfirmed),
            Ok(_) => {
                let revision = match self.head(&req.page_name).await {
                    Ok(Head::Present { uuid, parent, .. })
                        if prev.as_deref() != Some(uuid.as_str()) && parent == prev =>
                    {
                        Some(uuid)
                    }
                    _ => None,
                };
                CommitOutcome::Committed { revision }
            }
        };
        let CommitOutcome::Committed { revision: Some(_) } = &commit else {
            return finish(self, &mut rec, &base, commit, None);
        };
        if req.publication == Publication::LocalOnly {
            return finish(self, &mut rec, &base, commit, None);
        }

        // Record "publication unknown" *before* sync starts: a crash or lost
        // reply after this point must never read as "not published".
        let started = PublishOutcome::Unknown(ErrorCode::PublicationUnconfirmed);
        finish(self, &mut rec, &base, commit.clone(), Some(&started))?;
        let published = self.sync().await;
        finish(self, &mut rec, &base, commit, Some(&published))
    }
}

#[tool_router]
impl FossilWiki {
    /// Lists all wiki pages in the bound repository.
    #[tool(description = "List all wiki pages in the bound Fossil repository")]
    pub async fn list_wiki_pages(&self) -> Result<Json<types::ListWikiPagesResponse>, String> {
        let out = self
            .run(
                &["wiki", "list", "-R", &self.repo_arg()],
                None,
                self.inner.limits,
            )
            .await
            .map_err(|e| text_error(proc_error_code(e)))?;
        if !out.success() {
            return Err(text_error(ErrorCode::BadResponse));
        }
        let stdout = String::from_utf8_lossy(&out.stdout);
        Ok(Json(types::ListWikiPagesResponse {
            pages: parse_wiki_list(&stdout),
        }))
    }

    /// Reads the exact content and current revision of a page.
    #[tool(description = "Read the content and current revision of a wiki page")]
    pub async fn read_wiki_page(
        &self,
        args: Parameters<ReadWikiPageArgs>,
    ) -> Result<Json<types::ReadWikiPageResponse>, String> {
        if !valid_page_name(&args.0.page_name) {
            return Err(text_error(ErrorCode::InvalidArgument));
        }
        match self.head(&args.0.page_name).await.map_err(text_error)? {
            Head::Absent => Err(text_error(ErrorCode::PageNotFound)),
            Head::Present { uuid, content, .. } => {
                if content.len() > MAX_CONTENT_BYTES {
                    return Err(text_error(ErrorCode::BadResponse));
                }
                Ok(Json(types::ReadWikiPageResponse {
                    page_name: args.0.page_name,
                    content,
                    revision: uuid,
                }))
            }
        }
    }

    /// Creates or updates a page and returns a typed receipt.
    ///
    /// The receipt separates the local commit (`commit_state`) from
    /// publication (`publication_state`); `unknown` is never reported as
    /// failure. Repeating an `operation_id` with the same request replays the
    /// stored receipt and never commits twice. There is no lost-update
    /// protection yet: `previous_revision` is observed, not enforced.
    #[tool(
        description = "Create or update a wiki page; returns a typed receipt (commit_state, publication_state, revision)",
        output_schema = rmcp::handler::server::common::schema_for_type::<WriteToolOutput>()
    )]
    pub async fn write_wiki_page(
        &self,
        args: Parameters<WriteWikiPageArgs>,
    ) -> Result<CallToolResult, ErrorData> {
        if !self.inner.allow_local_writes {
            return fail(ErrorCode::WriteDisabled);
        }
        let req = match validate_write(&args.0) {
            Ok(r) => r,
            Err(c) => return fail(c),
        };
        if req.publication == Publication::SyncRepository && !self.inner.allow_repository_sync {
            return fail(ErrorCode::PublicationDenied);
        }
        let Ok(_guard) = self.inner.mutation.try_lock() else {
            return fail(ErrorCode::Busy);
        };
        let id = args.0.operation_id.as_str();
        let journal = match self.journal() {
            Ok(j) => j,
            Err(c) => return fail(c),
        };
        match journal.get(id) {
            Err(_) => return fail(ErrorCode::ReceiptStoreUnavailable),
            Ok(Some(rec)) => {
                if rec.request != req || rec.repo_id != self.repo_id() {
                    return fail(ErrorCode::IdempotencyConflict);
                }
                let retryable = rec.receipt.commit_state == types::CommitState::NotCommitted
                    && rec.receipt.retry_action == types::RetryAction::RetrySameOperation;
                if !retryable {
                    let ok = rec.receipt.is_success();
                    return receipt_result(rec.receipt, !ok);
                }
            }
            Ok(None) => {}
        }
        // Reserve (commit already "unknown") before any child can run.
        let rec = Record::reservation(self.repo_id(), id, req);
        if let Err(c) = self.persist(id, &rec) {
            return fail(c);
        }
        match self.execute(id, rec).await {
            Ok(receipt) => {
                let ok = receipt.is_success();
                receipt_result(receipt, !ok)
            }
            Err(c) => fail(c),
        }
    }

    /// Returns the stored receipt of an earlier write. Read-only.
    #[tool(
        description = "Return the stored receipt of an earlier write_wiki_page operation",
        output_schema = rmcp::handler::server::common::schema_for_type::<WriteToolOutput>()
    )]
    pub async fn wiki_operation_status(
        &self,
        args: Parameters<OperationStatusArgs>,
    ) -> Result<CallToolResult, ErrorData> {
        let journal = match self.journal() {
            Ok(j) => j,
            Err(c) => return fail(c),
        };
        match journal.get(&args.0.operation_id) {
            Ok(Some(rec)) if rec.repo_id == self.repo_id() => receipt_result(rec.receipt, false),
            Ok(_) | Err(JournalError::BadKey) => fail(ErrorCode::UnknownOperation),
            Err(_) => fail(ErrorCode::ReceiptStoreUnavailable),
        }
    }

    /// Inspects an operation; with `retry_publication`, re-runs only the sync
    /// of an already committed revision. Never creates a wiki artifact.
    #[tool(
        description = "Reconcile an earlier write: report its receipt, optionally retrying only the sync of a committed revision",
        output_schema = rmcp::handler::server::common::schema_for_type::<WriteToolOutput>()
    )]
    pub async fn wiki_reconcile_operation(
        &self,
        args: Parameters<ReconcileOperationArgs>,
    ) -> Result<CallToolResult, ErrorData> {
        let journal = match self.journal() {
            Ok(j) => j,
            Err(c) => return fail(c),
        };
        let id = args.0.operation_id.as_str();
        let rec = match journal.get(id) {
            Ok(Some(r)) if r.repo_id == self.repo_id() => r,
            Ok(_) | Err(JournalError::BadKey) => return fail(ErrorCode::UnknownOperation),
            Err(_) => return fail(ErrorCode::ReceiptStoreUnavailable),
        };
        if !args.0.retry_publication {
            return receipt_result(rec.receipt, false);
        }
        if !self.inner.allow_repository_sync {
            return fail(ErrorCode::PublicationDenied);
        }
        let eligible = rec.receipt.commit_state == types::CommitState::Committed
            && rec.receipt.revision.is_some()
            && rec.request.publication == Publication::SyncRepository
            && matches!(
                rec.receipt.publication_state,
                types::PublicationState::Pending | types::PublicationState::Unknown
            );
        if !eligible {
            return fail(ErrorCode::InvalidArgument);
        }
        let Ok(_guard) = self.inner.mutation.try_lock() else {
            return fail(ErrorCode::Busy);
        };
        let mut rec = rec;
        let base = ReceiptBase {
            repo_id: rec.receipt.repo_id.clone(),
            operation_id: id.to_string(),
            page_name: rec.receipt.page_name.clone(),
            previous_revision: rec.receipt.previous_revision.clone(),
        };
        let commit = CommitOutcome::Committed {
            revision: rec.receipt.revision.clone(),
        };
        let started = PublishOutcome::Unknown(ErrorCode::PublicationUnconfirmed);
        rec.receipt = build_receipt(&base, Publication::SyncRepository, &commit, Some(&started));
        if let Err(c) = self.persist(id, &rec) {
            return fail(c);
        }
        let published = self.sync().await;
        rec.receipt = build_receipt(
            &base,
            Publication::SyncRepository,
            &commit,
            Some(&published),
        );
        if let Err(c) = self.persist(id, &rec) {
            return fail(c);
        }
        let ok = rec.receipt.is_success();
        receipt_result(rec.receipt, !ok)
    }
}

impl ServerHandler for FossilWiki {
    fn get_info(&self) -> ServerInfo {
        ServerInfo {
            protocol_version: Default::default(),
            capabilities: ServerCapabilities::builder().enable_tools().build(),
            server_info: Default::default(),
            instructions: Some("MCP server bound to one Fossil wiki repository".to_string()),
        }
    }

    async fn list_tools(
        &self,
        _request: Option<rmcp::model::PaginatedRequestParams>,
        _context: rmcp::service::RequestContext<rmcp::RoleServer>,
    ) -> Result<rmcp::model::ListToolsResult, ErrorData> {
        Ok(rmcp::model::ListToolsResult {
            tools: self.tool_router.list_all(),
            meta: None,
            next_cursor: None,
        })
    }

    async fn call_tool(
        &self,
        request: rmcp::model::CallToolRequestParams,
        context: rmcp::service::RequestContext<rmcp::RoleServer>,
    ) -> Result<CallToolResult, ErrorData> {
        let tcc = rmcp::handler::server::tool::ToolCallContext::new(self, request, context);
        self.tool_router.call(tcc).await
    }

    fn get_tool(&self, name: &str) -> Option<rmcp::model::Tool> {
        self.tool_router.get(name).cloned()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_wiki_list_empty() {
        assert_eq!(parse_wiki_list(""), Vec::<String>::new());
    }

    #[test]
    fn test_parse_wiki_list_whitespace_and_blank_lines() {
        let pages = parse_wiki_list("  HomePage  \n\nAbout\n\n\nDocs/API\n");
        assert_eq!(pages, vec!["HomePage", "About", "Docs/API"]);
    }

    #[test]
    fn page_name_rules() {
        assert!(valid_page_name("Docs/API v2"));
        assert!(!valid_page_name(""));
        assert!(!valid_page_name("-R"));
        assert!(!valid_page_name("a\0b"));
        assert!(!valid_page_name("a\nb"));
        assert!(!valid_page_name(&"x".repeat(257)));
        assert!(valid_page_name(&"x".repeat(256)));
    }
}

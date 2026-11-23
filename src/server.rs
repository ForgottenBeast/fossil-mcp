//! MCP server implementation for Fossil SCM wiki operations.
//!
//! [`FossilWiki`] is bound to exactly one repository at construction
//! ([`FossilWiki::bind`]); nothing a client sends can change that binding.
//! The stable tool catalog is `list_wiki_pages`, `read_wiki_page`,
//! `write_wiki_page`, `wiki_operation_status` and `wiki_reconcile_operation`.
//! Writes and reconciliation are disabled unless the operator opts in. A sixth
//! tool, `wiki_backlinks`, is routed only when the backlinks flags are given.
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

pub mod backlinks;
pub mod binding;
pub mod operations;
pub mod outcome;
pub mod process;
pub mod secret;
pub mod types;

use backlinks::BacklinksService;
use binding::{RepositoryBinding, StartupError, WikiConfig};
use operations::{Journal, JournalError, Record, RepoIdentity, StoredRequest, valid_operation_id};
use outcome::{
    CommitOutcome, PublishOutcome, ReceiptBase, build_receipt, classify_sync, proc_error_code,
    resolve_retry,
};
use process::{Limits, ProcError, ProcOutput};
use types::{
    Backlink, Cursor, DEFAULT_BACKLINKS_LIMIT, ErrorCode, MAX_BACKLINKS_LIMIT, MAX_CONTENT_BYTES,
    MAX_PAGE_NAME_BYTES, OperationStatusArgs, Publication, ReadWikiPageArgs,
    ReconcileOperationArgs, WikiBacklinksArgs, WikiBacklinksResponse, WriteReceipt,
    WriteWikiPageArgs,
};

/// The highest blob id, read right before our commit starts.
///
/// `fossil wiki create|commit` prints no artifact id on 2.27 or 2.28 (only
/// "Created/Updated wiki page"), so identity is inferred: everything our
/// commit creates has a larger `rid` than anything that existed before it.
const SQL_MAX_RID: &str = "SELECT COALESCE(MAX(rid), 0) FROM blob";

/// Every wiki revision, newest first: `hex(tagname), rid, uuid`.
///
/// Constant: no request-derived text is ever interpolated; the page is
/// matched in Rust against the hex-decoded tag name.
const SQL_WIKI_REVISIONS: &str = "SELECT hex(t.tagname), x.rid, b.uuid \
FROM tagxref x JOIN tag t ON t.tagid=x.tagid JOIN blob b ON b.rid=x.rid \
WHERE substr(t.tagname, 1, 5)='wiki-' AND x.tagtype>0 ORDER BY x.rid DESC LIMIT 4097";

/// Row cap of [`SQL_WIKI_REVISIONS`] (the query asks for one more).
const MAX_REVISION_ROWS: usize = 4096;

/// The complete set of SQL strings this server hands to `fossil sql`.
#[doc(hidden)]
pub const ATTRIBUTION_SQL: &[&str] = &[SQL_MAX_RID, SQL_WIKI_REVISIONS];

/// Maximum concurrently running `fossil` children.
const MAX_ACTIVE_CHILDREN: usize = 4;

/// The `W` card payload of a wiki artifact: `W <size>\n<bytes>\n`.
fn wiki_body(artifact: &[u8]) -> Option<&[u8]> {
    let at = artifact.windows(3).position(|w| w == b"\nW ")? + 3;
    let rest = &artifact[at..];
    let nl = rest.iter().position(|b| *b == b'\n')?;
    let size: usize = std::str::from_utf8(&rest[..nl]).ok()?.parse().ok()?;
    rest.get(nl + 1..nl + 1 + size)
}

fn is_artifact_id(s: &str) -> bool {
    !s.is_empty() && s.bytes().all(|b| b.is_ascii_alphanumeric())
}

/// Decodes the hex text produced by SQL `hex()`; `None` when malformed.
fn unhex(s: &str) -> Option<Vec<u8>> {
    if !s.len().is_multiple_of(2) {
        return None;
    }
    s.as_bytes()
        .chunks(2)
        .map(|c| u8::from_str_radix(std::str::from_utf8(c).ok()?, 16).ok())
        .collect()
}

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
    Present { uuid: String, content: String },
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
    /// Identity of the bound repository; present when writes are enabled.
    identity: Option<RepoIdentity>,
    mutation: Mutex<()>,
    children: Semaphore,
    /// Present when the `wiki_backlinks` flag group was supplied.
    backlinks: Option<Arc<BacklinksService>>,
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

/// Tool error text for a failed sidecar exchange: the fixed text, plus the
/// index status when the sidecar reported one of its two known values.
fn backlinks_error(f: backlinks::Failure) -> String {
    match f.index_status {
        Some(status) => format!("{} (index status: {status})", text_error(f.code)),
        None => text_error(f.code),
    }
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
        let backlinks = cfg
            .backlinks
            .as_ref()
            .map(BacklinksService::new)
            .transpose()
            .map_err(|e| match e {
                backlinks::InitError::InvalidConfig => StartupError::InvalidBacklinksConfig,
                backlinks::InitError::Credential => StartupError::BacklinksCredentialUnavailable,
            })?
            .map(Arc::new);
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
        let mut wiki = Self {
            inner: Arc::new(Inner {
                binding,
                fossil_bin: cfg.fossil_bin,
                limits: cfg.limits,
                sync_limits,
                allow_local_writes: cfg.allow_local_writes,
                allow_repository_sync: cfg.allow_repository_sync,
                journal,
                identity: None,
                mutation: Mutex::new(()),
                children: Semaphore::new(MAX_ACTIVE_CHILDREN),
                backlinks,
            }),
            tool_router: Self::tool_router(),
        };
        // The tool is only routable (listed and callable) when configured.
        if wiki.inner.backlinks.is_none() {
            wiki.tool_router.remove_route("wiki_backlinks");
        }
        match wiki
            .run(
                &["wiki", "list", "-R", &wiki.repo_arg()],
                None,
                wiki.inner.limits,
            )
            .await
        {
            Ok(o) if o.success() => {}
            Err(ProcError::Spawn) => return Err(StartupError::FossilUnavailable),
            _ => return Err(StartupError::NotAFossilRepository),
        }
        if wiki.inner.journal.is_some() {
            let project_code = wiki.project_code().await?;
            let identity = RepoIdentity {
                project_code,
                path: wiki.repo_arg(),
            };
            Arc::get_mut(&mut wiki.inner)
                .expect("not yet shared")
                .identity = Some(identity);
        }
        Ok(wiki)
    }

    /// The Fossil project code of the bound repository (`fossil info`).
    async fn project_code(&self) -> Result<String, StartupError> {
        let out = self
            .run(&["info", "-R", &self.repo_arg()], None, self.inner.limits)
            .await
            .map_err(|_| StartupError::NotAFossilRepository)?;
        if !out.success() {
            return Err(StartupError::NotAFossilRepository);
        }
        String::from_utf8_lossy(&out.stdout)
            .lines()
            .find_map(|l| l.strip_prefix("project-code:"))
            .map(|v| v.trim().to_string())
            .filter(|v| !v.is_empty() && v.bytes().all(|b| b.is_ascii_alphanumeric()))
            .ok_or(StartupError::NotAFossilRepository)
    }

    fn identity(&self) -> Result<&RepoIdentity, ErrorCode> {
        self.inner
            .identity
            .as_ref()
            .ok_or(ErrorCode::ReceiptStoreUnavailable)
    }

    /// Whether a journal record belongs to the bound repository.
    fn same_repository(&self, rec: &Record) -> Result<bool, ErrorCode> {
        Ok(&rec.repository == self.identity()?)
    }

    /// Whether `uuid` exists as an artifact in the bound repository.
    async fn artifact_present(&self, uuid: &str) -> Result<bool, ErrorCode> {
        if uuid.is_empty() || !uuid.bytes().all(|b| b.is_ascii_alphanumeric()) {
            return Ok(false);
        }
        let out = self
            .run(
                &["artifact", uuid, "-R", &self.repo_arg()],
                None,
                self.inner.limits,
            )
            .await
            .map_err(proc_error_code)?;
        Ok(out.success())
    }

    /// A recorded revision must exist in the bound repository: the project
    /// code and path survive a restore from an older snapshot, the artifact
    /// does not.
    async fn verify_revision(&self, rec: &Record) -> Result<(), ErrorCode> {
        match rec.receipt.revision.as_deref() {
            None => Ok(()),
            Some(rev) => match self.artifact_present(rev).await? {
                true => Ok(()),
                false => Err(ErrorCode::JournalRepositoryMismatch),
            },
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
                content: p.content.unwrap_or_default(),
            }),
            _ => Err(ErrorCode::BadResponse),
        }
    }

    /// The highest blob id right now (see [`SQL_MAX_RID`]).
    async fn max_rid(&self) -> Option<u64> {
        let out = self
            .run(
                &["sql", "--readonly", "-R", &self.repo_arg(), SQL_MAX_RID],
                None,
                self.inner.limits,
            )
            .await
            .ok()
            .filter(ProcOutput::success)?;
        String::from_utf8_lossy(&out.stdout)
            .trim()
            .trim_matches('\'')
            .parse()
            .ok()
    }

    /// Identify the artifact this write created.
    ///
    /// `baseline` is the highest blob id read just before our commit ran, so
    /// the page revisions with a larger `rid` are exactly those created
    /// meanwhile, by us or by a concurrent writer, whatever their parent.
    /// The one accepted is the single such revision whose wiki body equals
    /// the bytes we wrote, and only if every candidate was read and parsed:
    /// a failed fetch (nonzero exit, runner error, timeout, output cap) or a
    /// missing/unparseable W card gives `None`, as do zero or several
    /// matches (a concurrent writer with the same bytes is indistinguishable)
    /// and a listing that does not reach back to the baseline
    /// (`revision_unresolved`). So another writer's revision is returned only
    /// if it is the sole readable same-bytes revision after the baseline,
    /// which needs ids to stay monotonic: a purge or restore mid-write can
    /// break that, and no content check can detect it.
    async fn attribute(&self, baseline: u64, page: &str, content: &[u8]) -> Option<String> {
        let repo = self.repo_arg();
        let mut limits = self.inner.limits;
        limits.stdout_max = limits.stdout_max.saturating_mul(4);
        let listed = self
            .run(
                &["sql", "--readonly", "-R", &repo, SQL_WIKI_REVISIONS],
                None,
                limits,
            )
            .await
            .ok()
            .filter(ProcOutput::success)?;
        let want_tag = format!("wiki-{page}");
        let stdout = String::from_utf8_lossy(&listed.stdout);
        let rows: Vec<(&str, u64, &str)> = stdout
            .lines()
            .map(|l| {
                let mut f = l.split([',', '|']).map(|v| v.trim().trim_matches('\''));
                Some((f.next()?, f.next()?.parse().ok()?, f.next()?))
            })
            .collect::<Option<_>>()?;
        if rows.len() > MAX_REVISION_ROWS && rows.last().is_none_or(|r| r.1 > baseline) {
            return None; // the cap hid part of the window after the baseline
        }
        let candidates: Vec<&str> = rows
            .iter()
            .take(MAX_REVISION_ROWS)
            .filter(|(tag, rid, uuid)| {
                *rid > baseline
                    && is_artifact_id(uuid)
                    && unhex(tag).is_some_and(|t| t == want_tag.as_bytes())
            })
            .map(|r| r.2)
            .collect();
        let mut matched = None;
        for uuid in candidates {
            let art = self
                .run(&["artifact", uuid, "-R", &repo], None, limits)
                .await
                .ok()?;
            if !art.success() {
                return None; // an unread candidate could be ours: no uniqueness claim
            }
            let body = wiki_body(&art.stdout)?; // no parseable W card: same
            if body == content {
                if matched.is_some() {
                    return None;
                }
                matched = Some(uuid.to_string());
            }
        }
        matched
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

        // No baseline, no commit: attribution could never be proven afterwards.
        let Some(baseline) = self.max_rid().await else {
            let never = CommitOutcome::NeverRan(ErrorCode::PreflightFailed);
            return finish(self, &mut rec, &base, never, None);
        };
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
                let revision = self
                    .attribute(baseline, &req.page_name, req.content.as_bytes())
                    .await;
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
    #[tool(
        description = "List all wiki pages in the bound Fossil repository",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
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
    #[tool(
        description = "Read the content and current revision of a wiki page",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
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

    /// Lists the pages that link to `page`, from the repository's backlinks
    /// sidecar. Read-only; present only when configured at startup.
    #[tool(
        description = "List the wiki pages that link to a page, from the repository's backlinks service (paginated, read-only)",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = true
        )
    )]
    pub async fn wiki_backlinks(
        &self,
        args: Parameters<WikiBacklinksArgs>,
    ) -> Result<Json<WikiBacklinksResponse>, String> {
        let args = args.0;
        let limit = args.limit.unwrap_or(DEFAULT_BACKLINKS_LIMIT);
        let cursor = match args.cursor.as_deref() {
            None => None,
            Some(c) => {
                Some(Cursor::parse(c).ok_or_else(|| text_error(ErrorCode::InvalidArgument))?)
            }
        };
        if !valid_page_name(&args.page) || !(1..=MAX_BACKLINKS_LIMIT).contains(&limit) {
            return Err(text_error(ErrorCode::InvalidArgument));
        }
        let service = self
            .inner
            .backlinks
            .clone()
            .ok_or_else(|| text_error(ErrorCode::InvalidArgument))?;
        let page = args.page.clone();
        let fetched = tokio::task::spawn_blocking(move || service.fetch(&page))
            .await
            .map_err(|_| text_error(ErrorCode::BadResponse))?
            .map_err(backlinks_error)?;
        if fetched.repo_id != self.repo_id() {
            return Err(text_error(ErrorCode::BacklinksRepoMismatch));
        }
        if fetched.page != args.page {
            return Err(text_error(ErrorCode::BadResponse));
        }
        let total = fetched.inbound.len() as u64;
        let start = match cursor {
            None => 0,
            Some(c) if c.generation != fetched.generation => {
                return Err(text_error(ErrorCode::CursorStale));
            }
            Some(c) if c.offset > total => return Err(text_error(ErrorCode::InvalidArgument)),
            Some(c) => c.offset,
        };
        let end = (start + u64::from(limit)).min(total);
        let next_cursor = (end < total).then(|| {
            Cursor {
                generation: fetched.generation,
                offset: end,
            }
            .to_string()
        });
        Ok(Json(WikiBacklinksResponse {
            schema_version: backlinks::SCHEMA_VERSION.to_string(),
            repo_id: self.repo_id().to_string(),
            page: fetched.page,
            status: "current".to_string(),
            checked_at: fetched.checked_at,
            generation: fetched.generation,
            inbound: fetched.inbound[start as usize..end as usize]
                .iter()
                .map(|p| Backlink {
                    source_page: p.clone(),
                })
                .collect(),
            total_inbound: total,
            next_cursor,
        }))
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
        annotations(read_only_hint = false, destructive_hint = true, idempotent_hint = true, open_world_hint = true),
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
                match self.same_repository(&rec) {
                    Ok(true) => {}
                    Ok(false) => return fail(ErrorCode::JournalRepositoryMismatch),
                    Err(c) => return fail(c),
                }
                let retryable = rec.receipt.commit_state == types::CommitState::NotCommitted
                    && rec.receipt.retry_action == types::RetryAction::RetrySameOperation;
                if !retryable {
                    if let Err(c) = self.verify_revision(&rec).await {
                        return fail(c);
                    }
                    let ok = rec.receipt.is_success();
                    return receipt_result(rec.receipt, !ok);
                }
            }
            Ok(None) => {}
        }
        // Reserve (commit already "unknown") before any child can run.
        let identity = match self.identity() {
            Ok(i) => i,
            Err(c) => return fail(c),
        };
        let rec = Record::reservation(self.repo_id(), identity, id, req);
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
        annotations(read_only_hint = true, destructive_hint = false, idempotent_hint = true, open_world_hint = false),
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
            Ok(Some(rec)) if rec.repo_id == self.repo_id() => match self.same_repository(&rec) {
                Ok(true) => match self.verify_revision(&rec).await {
                    Ok(()) => receipt_result(rec.receipt, false),
                    Err(c) => fail(c),
                },
                Ok(false) => fail(ErrorCode::JournalRepositoryMismatch),
                Err(c) => fail(c),
            },
            Ok(_) | Err(JournalError::BadKey) => fail(ErrorCode::UnknownOperation),
            Err(_) => fail(ErrorCode::ReceiptStoreUnavailable),
        }
    }

    /// Inspects an operation; with `retry_publication`, re-runs only the sync
    /// of an already committed revision. Never creates a wiki artifact.
    #[tool(
        description = "Reconcile an earlier write: report its receipt, optionally retrying only the sync of a committed revision",
        annotations(read_only_hint = false, destructive_hint = true, idempotent_hint = true, open_world_hint = true),
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
        match self.same_repository(&rec) {
            Ok(true) => {}
            Ok(false) => return fail(ErrorCode::JournalRepositoryMismatch),
            Err(c) => return fail(c),
        }
        if let Err(c) = self.verify_revision(&rec).await {
            return fail(c);
        }
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
        // Re-check under the lock: eligibility already guarantees a revision.
        if let Err(c) = self.verify_revision(&rec).await {
            return fail(c);
        }
        let prior = rec.receipt.publication_state;
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
        let published = resolve_retry(prior, self.sync().await);
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

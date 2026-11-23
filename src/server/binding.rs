//! Immutable repository binding and startup configuration.
//!
//! The repository alias and path are fixed once, at process start, by the
//! operator. No request can change them and no default is inferred from the
//! environment or working directory. This is namespace isolation, not caller
//! authentication: every harness subprocess shares the owner's OS authority,
//! and `repo_id` is an identifier, never an authorization token.

use crate::server::operations::{DEFAULT_JOURNAL_CAP, valid_operation_id};
use crate::server::process::Limits;
use std::path::PathBuf;
use std::time::Duration;

/// Fixed startup configuration of the `wiki_backlinks` tool. All fields come
/// from operator flags; none is reachable from a tool argument.
#[derive(Debug, Clone)]
pub struct BacklinksConfig {
    /// Origin of this repository's sidecar (`https://host[:port]`).
    pub url: String,
    /// OIDC issuer (`https://host[:port]`); the token endpoint is
    /// `<issuer>/oauth/v2/token`.
    pub issuer: String,
    /// Path of the Zitadel machine-user key file (never its content).
    pub key_file: PathBuf,
    /// Audience scopes requested besides `openid`.
    pub audience_scopes: Vec<String>,
    /// Deadline of each HTTP call (1000 to 60000 ms).
    pub timeout: Duration,
}

/// Operator-supplied startup configuration.
#[derive(Debug, Clone)]
pub struct WikiConfig {
    /// Alias for the bound repository (1-64 ASCII letters, digits, `_`, `-`).
    pub repo_id: String,
    /// Path of the Fossil repository file. Symlinks are rejected.
    pub repository: PathBuf,
    /// The `fossil` executable to run.
    pub fossil_bin: PathBuf,
    /// Permit `write_wiki_page` / reconcile. Off by default (read-only).
    pub allow_local_writes: bool,
    /// Permit `publication: sync_repository`. Off by default.
    pub allow_repository_sync: bool,
    /// Private directory for the receipt journal; required for writes.
    pub state_dir: Option<PathBuf>,
    /// Budgets for local commands.
    pub limits: Limits,
    /// Deadline for `fossil sync`.
    pub sync_deadline: Duration,
    /// Journal size cap in bytes.
    pub journal_cap: u64,
    /// Enables the `wiki_backlinks` tool; absent means the tool is not
    /// listed and cannot be called.
    pub backlinks: Option<BacklinksConfig>,
}

impl WikiConfig {
    /// Read-only configuration with default budgets.
    pub fn new(repo_id: impl Into<String>, repository: impl Into<PathBuf>) -> Self {
        Self {
            repo_id: repo_id.into(),
            repository: repository.into(),
            fossil_bin: PathBuf::from("fossil"),
            allow_local_writes: false,
            allow_repository_sync: false,
            state_dir: None,
            limits: Limits::default(),
            sync_deadline: Duration::from_secs(30),
            journal_cap: DEFAULT_JOURNAL_CAP,
            backlinks: None,
        }
    }
}

/// Why startup binding failed. Messages are fixed and contain no paths.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StartupError {
    /// The alias is empty, too long or has forbidden characters.
    InvalidRepoId,
    /// The repository path is missing, a symlink, a directory or empty.
    InvalidRepositoryFile,
    /// The `fossil` executable could not be started.
    FossilUnavailable,
    /// `fossil` did not accept the file as a repository.
    NotAFossilRepository,
    /// Writes were enabled without a state directory.
    StateDirRequired,
    /// The state directory or its lock is unusable.
    StateDirUnavailable,
    /// The `wiki_backlinks` configuration is invalid.
    InvalidBacklinksConfig,
    /// The backlinks key file is missing, unsafe or not a usable key (checked
    /// once at startup; it is read again on every token refresh).
    BacklinksCredentialUnavailable,
}

impl std::fmt::Display for StartupError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::InvalidRepoId => "invalid --repo-id",
            Self::InvalidRepositoryFile => {
                "repository must be an existing, non-empty regular file (symlinks are rejected)"
            }
            Self::FossilUnavailable => "the fossil executable could not be started",
            Self::NotAFossilRepository => "fossil did not accept the file as a repository",
            Self::StateDirRequired => "--allow-local-writes requires --state-dir",
            Self::StateDirUnavailable => {
                "state directory is unusable or locked (a stale LOCK needs operator removal)"
            }
            Self::InvalidBacklinksConfig => {
                "invalid backlinks configuration (https origins without a path, at least one \
                 audience scope, a timeout of 1000-60000 ms)"
            }
            Self::BacklinksCredentialUnavailable => {
                "the backlinks key file is missing, unsafe or not a usable key \
                 (regular file, no symlink, at most 16 KiB, no access for others)"
            }
        })
    }
}

impl std::error::Error for StartupError {}

/// The validated, immutable binding.
#[derive(Debug)]
pub struct RepositoryBinding {
    pub(crate) repo_id: String,
    pub(crate) path: PathBuf,
}

impl RepositoryBinding {
    /// Alias of the bound repository.
    pub fn repo_id(&self) -> &str {
        &self.repo_id
    }

    /// Check alias and file shape, canonicalizing the path.
    pub(crate) fn check(cfg: &WikiConfig) -> Result<Self, StartupError> {
        if !valid_operation_id(&cfg.repo_id) {
            return Err(StartupError::InvalidRepoId);
        }
        let meta = std::fs::symlink_metadata(&cfg.repository)
            .map_err(|_| StartupError::InvalidRepositoryFile)?;
        if meta.file_type().is_symlink() || !meta.is_file() || meta.len() == 0 {
            return Err(StartupError::InvalidRepositoryFile);
        }
        let path = std::fs::canonicalize(&cfg.repository)
            .map_err(|_| StartupError::InvalidRepositoryFile)?;
        Ok(Self {
            repo_id: cfg.repo_id.clone(),
            path,
        })
    }
}

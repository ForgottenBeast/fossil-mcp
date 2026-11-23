//! Fossil MCP server binary (stdio transport).
//!
//! The repository is bound once, at startup; there is no runtime
//! reconfiguration, no environment fallback and no default.
//!
//! ```bash
//! # read-only
//! fossil-mcp --repo-id notes -R /path/to/repo.fossil
//! # owner-local writes, with a private receipt journal
//! fossil-mcp --repo-id notes -R /path/to/repo.fossil \
//!     --allow-local-writes --state-dir /path/to/private/state
//! ```
//!
//! The optional `wiki_backlinks` tool needs the whole flag group; without it
//! the tool does not exist. The key file is checked at startup, read again on
//! every token refresh and is never taken from the environment or an argument.
//!
//! ```bash
//! fossil-mcp --repo-id notes -R /path/to/repo.fossil \
//!     --backlinks-url https://sidecar.example \
//!     --backlinks-issuer https://issuer.example \
//!     --backlinks-key-file /run/secrets/fossil-mcp/notes-key.json \
//!     --backlinks-audience-scope urn:zitadel:iam:org:project:id:PROJECT:aud
//! ```
//!
//! Logs go to stderr so stdout carries only JSON-RPC.

use anyhow::Result;
use clap::Parser;
use fossil_mcp::{BacklinksConfig, FossilWiki, WikiConfig};
use rmcp::ServiceExt;
use std::path::PathBuf;
use std::time::Duration;
use tokio::io::{stdin, stdout};

/// Command-line arguments. Alias and repository are mandatory.
#[derive(Parser, Debug)]
#[command(author, version, about = "MCP server bound to one Fossil wiki repository", long_about = None)]
struct Args {
    /// Alias for the bound repository (1-64 ASCII letters, digits, `_`, `-`).
    #[arg(long, value_name = "ALIAS")]
    repo_id: String,
    /// Path to the Fossil repository file (symlinks are rejected).
    #[arg(short = 'R', long = "repository", value_name = "FILE")]
    repository: PathBuf,
    /// Enable write_wiki_page and reconcile (requires --state-dir).
    #[arg(long)]
    allow_local_writes: bool,
    /// Allow publication: sync_repository (may publish all sharable artifacts).
    #[arg(long)]
    allow_repository_sync: bool,
    /// Private (0700) directory for the receipt journal.
    #[arg(long, value_name = "DIR")]
    state_dir: Option<PathBuf>,
    /// The fossil executable to run.
    #[arg(long, value_name = "PATH", default_value = "fossil")]
    fossil_bin: PathBuf,
    /// Origin of this repository's backlinks sidecar (https, no path).
    #[arg(long, value_name = "URL", requires_all = ["backlinks_issuer", "backlinks_key_file", "backlinks_audience_scope"])]
    backlinks_url: Option<String>,
    /// OIDC issuer of the machine user (https, no path).
    #[arg(long, value_name = "URL", requires_all = ["backlinks_url", "backlinks_key_file", "backlinks_audience_scope"])]
    backlinks_issuer: Option<String>,
    /// Zitadel machine-user key file (mode 0600/0640, not a symlink).
    #[arg(long, value_name = "FILE", requires_all = ["backlinks_url", "backlinks_issuer", "backlinks_audience_scope"])]
    backlinks_key_file: Option<PathBuf>,
    /// Audience scope to request besides `openid` (repeatable).
    #[arg(long, value_name = "SCOPE", requires_all = ["backlinks_url", "backlinks_issuer", "backlinks_key_file"])]
    backlinks_audience_scope: Vec<String>,
    /// Deadline of each backlinks HTTP call in milliseconds.
    #[arg(
        long,
        value_name = "MS",
        default_value_t = 10_000,
        value_parser = clap::value_parser!(u64).range(1000..=60_000),
        requires = "backlinks_url"
    )]
    backlinks_timeout_ms: u64,
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .with_writer(std::io::stderr)
        .init();

    let args = Args::parse();
    let mut cfg = WikiConfig::new(args.repo_id, args.repository);
    cfg.fossil_bin = args.fossil_bin;
    cfg.allow_local_writes = args.allow_local_writes;
    cfg.allow_repository_sync = args.allow_repository_sync;
    cfg.state_dir = args.state_dir;
    if let (Some(url), Some(issuer), Some(key_file)) = (
        args.backlinks_url,
        args.backlinks_issuer,
        args.backlinks_key_file,
    ) {
        cfg.backlinks = Some(BacklinksConfig {
            url,
            issuer,
            key_file,
            audience_scopes: args.backlinks_audience_scope,
            timeout: Duration::from_millis(args.backlinks_timeout_ms),
        });
    }

    // Validation failure exits here, before any MCP service starts.
    let wiki = FossilWiki::bind(cfg).await?;
    tracing::info!(repo_id = wiki.repo_id(), "repository bound");

    let server = wiki.serve((stdin(), stdout())).await?;
    server.waiting().await?;
    Ok(())
}

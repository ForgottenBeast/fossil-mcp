//! # Fossil MCP Server
//!
//! A [Model Context Protocol (MCP)](https://modelcontextprotocol.io) server for
//! [Fossil SCM](https://fossil-scm.org) wiki pages, bound at startup to exactly
//! one repository.
//!
//! ## Tools
//!
//! - `list_wiki_pages` / `read_wiki_page` (the read returns the page `revision`)
//! - `write_wiki_page`: idempotent by `operation_id`, returns a typed receipt
//!   separating `commit_state` from `publication_state`
//! - `wiki_operation_status` / `wiki_reconcile_operation`: replay and
//!   reconcile receipts (never re-commit)
//!
//! Writes are disabled unless the operator starts the server with
//! `--allow-local-writes --state-dir <private dir>`; `publication:
//! sync_repository` additionally needs `--allow-repository-sync`.
//! There are no credential fields, no runtime repository selection and no
//! HTTP client. Remote authority and compare-and-swap are a separate gate;
//! the receipt's `previous_revision`/`revision` fields are where it plugs in.
//!
//! ## Example
//!
//! ```rust,no_run
//! use fossil_mcp::{FossilWiki, WikiConfig};
//!
//! # async fn run() -> Result<(), Box<dyn std::error::Error>> {
//! let mut cfg = WikiConfig::new("notes", "/path/to/repo.fossil");
//! cfg.allow_local_writes = true;
//! cfg.state_dir = Some("/path/to/private/state".into());
//! let wiki = FossilWiki::bind(cfg).await?;
//! println!("bound to {}", wiki.repo_id());
//! # Ok(())
//! # }
//! ```
//!
//! ## Testing
//!
//! ```bash
//! cargo test --locked --all-targets && cargo test --locked --doc
//! ```
//!
//! Tests build throwaway repositories with the `fossil` binary under a
//! temporary directory and never touch a real wiki.
//!
//! ## Assurance
//!
//! The TLA+ models in this repository are historical and do not certify this
//! implementation; see `TLA_SPECIFICATION.md` for the invariant-to-test table.
//!
//! ## Modules
//!
//! - [`server`]: handler, binding, process runner, receipt journal
//! - [`server::types`]: wire types (the schema authority)

pub mod server;

pub use server::binding::{RepositoryBinding, StartupError, WikiConfig};
pub use server::process::Limits;
pub use server::types::{ReadWikiPageArgs, ReadWikiPageResponse, WriteReceipt, WriteWikiPageArgs};
pub use server::{FossilWiki, WriteToolOutput};

//! # Fossil MCP Server
//!
//! A [Model Context Protocol (MCP)](https://modelcontextprotocol.io) server that provides
//! programmatic access to [Fossil SCM](https://fossil-scm.org) wiki pages.
//!
//! ## Overview
//!
//! This library exposes three MCP tools for interacting with Fossil wiki pages:
//!
//! - **`list_wiki_pages`** - List all wiki pages in a repository
//! - **`read_wiki_page`** - Read the content of a specific wiki page
//! - **`write_wiki_page`** - Create or update a wiki page with optional synchronization
//!
//! ## Quick Start
//!
//! ```rust,no_run
//! use fossil_mcp::FossilWiki;
//! use std::path::PathBuf;
//!
//! #[tokio::main]
//! async fn main() {
//!     // Create a handler for your Fossil repository
//!     let wiki = FossilWiki::new(PathBuf::from("/path/to/repo.fossil"));
//!
//!     // Use the handler with MCP server infrastructure
//!     // (typically called by the MCP server binary)
//! }
//! ```
//!
//! ## Architecture
//!
//! The server uses a stdio-based transport, communicating via JSON-RPC 2.0 messages.
//! All operations execute `fossil` commands with the `-R` flag, allowing interaction
//! with any Fossil repository without requiring a checkout directory.
//!
//! ### Key Components
//!
//! - **`FossilWiki`**: Main handler struct implementing MCP tool methods
//! - **`server::types`**: Request/response types with JSON schema definitions
//! - **`server::sync`**: Synchronization logic with error categorization
//!
//! ## Synchronization Features
//!
//! The `write_wiki_page` tool includes intelligent synchronization:
//!
//! - **`skip_sync`** - Skip repository synchronization after writing
//! - **`force_write`** - Allow write to succeed even on sync errors
//! - **Error categorization** - Distinguishes blocking (merge conflicts) from
//!   non-blocking (network, no remote) sync errors
//!
//! ## Example: Writing a Wiki Page
//!
//! ```rust,no_run
//! use fossil_mcp::{FossilWiki, WriteWikiPageArgs};
//! use rmcp::handler::server::wrapper::Parameters;
//! use std::path::PathBuf;
//!
//! # async fn example() -> Result<(), Box<dyn std::error::Error>> {
//! let wiki = FossilWiki::new(PathBuf::from("/path/to/repo.fossil"));
//!
//! let args = Parameters(WriteWikiPageArgs {
//!     page_name: "HomePage".to_string(),
//!     content: "# Welcome\n\nWelcome to the wiki!".to_string(),
//!     mimetype: Some("text/x-markdown".to_string()),
//!     skip_sync: false,  // Attempt sync after write
//!     force_write: false, // Fail on merge conflicts
//! });
//!
//! let response = wiki.write_wiki_page(args).await?;
//! println!("Page written: {}", response.0.page_name);
//!
//! // Check sync status
//! if let Some(sync_status) = response.0.sync_status {
//!     if !sync_status.succeeded {
//!         eprintln!("Sync failed: {:?}", sync_status.error_message);
//!     }
//! }
//! # Ok(())
//! # }
//! ```
//!
//! ## Command-Line Usage
//!
//! The binary (`fossil-mcp`) runs an MCP server on stdio:
//!
//! ```bash
//! fossil-mcp -R /path/to/repo.fossil
//! ```
//!
//! See the [MCP documentation](https://modelcontextprotocol.io) for client integration.
//!
//! ## Testing
//!
//! Run the test suite with:
//!
//! ```bash
//! cargo test
//! ```
//!
//! For integration tests with a real Fossil repository:
//!
//! ```bash
//! cargo test --test fossil_wiki_integration
//! ```
//!
//! ## Formal Verification
//!
//! The synchronization protocol is formally specified in TLA+ with model
//! checking verification. See `TLA_SPECIFICATION.md` for details.
//!
//! ## Modules
//!
//! - [`server`] - MCP server implementation and tool handlers
//! - [`server::types`] - Request/response type definitions
//! - [`server::sync`] - Repository synchronization logic

pub mod server;

// Re-export commonly used types for convenience
pub use server::FossilWiki;
pub use server::types::{
    ReadWikiPageArgs, ReadWikiPageResponse, WriteWikiPageArgs, WriteWikiPageResponse,
};

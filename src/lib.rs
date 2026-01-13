//! # Fossil MCP Server
//!
//! This library provides MCP (Model Context Protocol) server functionality
//! for interacting with Fossil SCM wiki pages.
//!
//! ## Modules
//!
//! - `state`: Application state management
//! - `types`: Type definitions for tool arguments
//! - `handlers`: MCP tool handler implementations
//! - `server`: MCP router implementation

pub mod handlers;
pub mod server;
pub mod state;
pub mod types;

// Re-export commonly used types for convenience
pub use server::FossilRouter;
pub use state::AppState;
pub use types::{ListWikiPagesArgs, ReadWikiPageArgs, WriteWikiPageArgs};

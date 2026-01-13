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

pub mod server;

// Re-export commonly used types for convenience
pub use server::FossilWiki;
pub use server::types::{
    ListWikiPagesArgs, ListWikiPagesResponse, ReadWikiPageArgs, ReadWikiPageResponse,
    WriteWikiPageArgs, WriteWikiPageResponse,
};

# Introduction

**Fossil MCP Server** is a [Model Context Protocol (MCP)](https://modelcontextprotocol.io) server that provides programmatic access to [Fossil SCM](https://fossil-scm.org) wiki pages.

## What is MCP?

The Model Context Protocol is an open protocol that enables seamless integration between AI applications and external data sources. MCP servers expose tools that AI models can use to interact with systems and services.

## What is Fossil?

Fossil is a simple, high-reliability, distributed software configuration management system with integrated bug tracking, wiki, forum, and technote capabilities.

## Features

- **📋 List Pages**: Retrieve all wiki pages in a repository
- **📖 Read Pages**: Get the content of specific wiki pages
- **✍️ Write Pages**: Create or update wiki pages with markdown or fossil-wiki syntax
- **🔄 Smart Sync**: Intelligent synchronization with error categorization
- **🔒 Type Safe**: Full type definitions with JSON schema validation
- **✅ Verified**: Formal TLA+ specifications with model checking
- **🚀 Fast**: Efficient Rust implementation with async I/O

## Use Cases

- **AI-Powered Documentation**: Let AI assistants read and update your project wiki
- **Automated Updates**: Programmatically maintain wiki pages from CI/CD
- **Documentation Generation**: Generate wiki pages from code analysis
- **Knowledge Base Integration**: Connect your wiki to AI knowledge systems

## Quick Example

```json
// List all wiki pages
{"method": "tools/call", "params": {"name": "list_wiki_pages"}}

// Read a specific page
{"method": "tools/call", "params": {
  "name": "read_wiki_page",
  "arguments": {"page_name": "HomePage"}
}}

// Write a page with sync
{"method": "tools/call", "params": {
  "name": "write_wiki_page",
  "arguments": {
    "page_name": "API/Reference",
    "content": "# API Documentation\n\nVersion 2.0...",
    "mimetype": "text/x-markdown",
    "skip_sync": false
  }
}}
```

## Architecture

```
┌─────────────┐
│ MCP Client  │ (Claude Desktop, CLI, etc.)
└──────┬──────┘
       │ JSON-RPC over stdio
┌──────▼──────────┐
│  fossil-mcp     │
│  MCP Server     │
└──────┬──────────┘
       │ Execute commands
┌──────▼──────────┐
│ fossil -R repo  │ (Fossil SCM)
└─────────────────┘
       │
┌──────▼──────────┐
│  SQLite DB      │ (Repository file)
└─────────────────┘
```

## Status

**Current Version**: 0.1.0 (unreleased 0.2.0 contract in progress; see CHANGELOG.md)
**Status**: Local, owner-operated use only; remote authority and lost-update protection are not implemented
**Tests**: run `cargo test --locked --all-targets` and `cargo test --locked --doc`
**Formal Verification**: none for the current code. The historical TLA+ models are retired; see the appendix

## Getting Started

Continue to the [User Guide](./user-guide/getting-started.md) to start using the Fossil MCP server.

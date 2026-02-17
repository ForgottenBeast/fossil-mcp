# Quick Start

This guide demonstrates the three main operations: listing, reading, and writing wiki pages.

## Setup

First, start the MCP server:

```bash
fossil-mcp -R /path/to/your/repo.fossil
```

The server communicates via stdio using JSON-RPC 2.0 protocol.

## MCP Protocol Handshake

Every MCP session starts with initialization:

```json
// 1. Send initialize request
{
  "jsonrpc": "2.0",
  "id": 1,
  "method": "initialize",
  "params": {
    "protocolVersion": "2024-11-05",
    "capabilities": {},
    "clientInfo": {"name": "my-client", "version": "1.0"}
  }
}

// 2. Server responds with capabilities
{
  "jsonrpc": "2.0",
  "id": 1,
  "result": {
    "protocolVersion": "2024-11-05",
    "capabilities": {"tools": {}},
    "serverInfo": {"name": "rmcp", "version": "0.12.0"}
  }
}

// 3. Send initialized notification
{
  "jsonrpc": "2.0",
  "method": "notifications/initialized"
}
```

## List All Wiki Pages

Get a list of all pages in the repository:

```json
{
  "jsonrpc": "2.0",
  "id": 2,
  "method": "tools/call",
  "params": {
    "name": "list_wiki_pages",
    "arguments": {}
  }
}
```

**Response:**
```json
{
  "jsonrpc": "2.0",
  "id": 2,
  "result": {
    "content": [{
      "type": "text",
      "text": "{\"pages\":[\"HomePage\",\"About\",\"Docs/API\"]}"
    }]
  }
}
```

## Read a Wiki Page

Retrieve the content of a specific page:

```json
{
  "jsonrpc": "2.0",
  "id": 3,
  "method": "tools/call",
  "params": {
    "name": "read_wiki_page",
    "arguments": {
      "page_name": "HomePage"
    }
  }
}
```

**Response:**
```json
{
  "jsonrpc": "2.0",
  "id": 3,
  "result": {
    "content": [{
      "type": "text",
      "text": "{\"page_name\":\"HomePage\",\"content\":\"# Welcome\\n\\nWelcome to the wiki!\"}"
    }]
  }
}
```

## Write a Wiki Page

Create or update a page:

```json
{
  "jsonrpc": "2.0",
  "id": 4,
  "method": "tools/call",
  "params": {
    "name": "write_wiki_page",
    "arguments": {
      "page_name": "NewPage",
      "content": "# New Page\\n\\nThis is new content.",
      "mimetype": "text/x-markdown",
      "skip_sync": true
    }
  }
}
```

**Response:**
```json
{
  "jsonrpc": "2.0",
  "id": 4,
  "result": {
    "content": [{
      "type": "text",
      "text": "{\"success\":true,\"page_name\":\"NewPage\",\"message\":\"Wiki page written successfully\"}"
    }]
  }
}
```

## With Synchronization

To sync with a remote repository after writing:

```json
{
  "jsonrpc": "2.0",
  "id": 5,
  "method": "tools/call",
  "params": {
    "name": "write_wiki_page",
    "arguments": {
      "page_name": "UpdatedPage",
      "content": "# Updated Content",
      "mimetype": "text/x-markdown",
      "skip_sync": false,
      "force_write": false
    }
  }
}
```

**Response with sync status:**
```json
{
  "jsonrpc": "2.0",
  "id": 5,
  "result": {
    "content": [{
      "type": "text",
      "text": "{\"success\":true,\"page_name\":\"UpdatedPage\",\"message\":\"Wiki page written successfully\",\"sync_status\":{\"attempted\":true,\"succeeded\":false,\"error_type\":\"NoRemoteConfigured\",\"error_message\":\"No remote URL configured for this repository.\",\"can_force_write\":false}}"
    }]
  }
}
```

## Next Steps

- [Synchronization Guide](./synchronization.md) - Learn about sync options
- [API Reference](../api/tools.md) - Detailed parameter documentation
- [Troubleshooting](./troubleshooting.md) - Common issues and solutions

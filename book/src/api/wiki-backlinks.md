# wiki_backlinks

Lists the wiki pages that link to a page, from the repository's backlinks service.
Read-only, idempotent, open-world. The tool is **absent** from the catalog unless the
server is started with the whole flag group:

```bash
fossil-mcp --repo-id notes -R /path/to/repo.fossil \
  --backlinks-url https://sidecar.example \
  --backlinks-issuer https://issuer.example \
  --backlinks-key-file /run/secrets/fossil-mcp/notes-key.json \
  --backlinks-audience-scope urn:zitadel:iam:org:project:id:PROJECT:aud
```

- `--backlinks-url`, `--backlinks-issuer`: `https://host[:port]`, no path. Plain `http` is
  accepted only for `127.0.0.1` and `[::1]`.
- `--backlinks-key-file`: Zitadel machine-user key JSON. It must be a regular file (not a
  symlink), at most 16 KiB, with no access for others and no group write. It is read on every
  token refresh, so a rotated key needs no restart. The credential is never taken from the
  environment or from a tool argument.
- `--backlinks-audience-scope`: repeatable; `openid` is always requested.
- `--backlinks-timeout-ms`: per HTTP call, 1000-60000, default 10000.

## Parameters

| name | type | notes |
|---|---|---|
| `page` | string, required | 1-256 bytes, no NUL/CR/LF, not starting with `-` |
| `cursor` | string, optional | previous `next_cursor` (`<generation>:<offset>`) |
| `limit` | integer, optional | 1-200, default 100 |

## Response

`{schema_version, repo_id, page, status, checked_at, generation, inbound, total_inbound,
next_cursor}`; `inbound` is `[{source_page}]`, `next_cursor` is null on the last page. A cursor
from an older index generation fails with `cursor_stale`.

## Errors

Fixed codes, never including a token, key, path or response body: `page_not_found`,
`invalid_argument`, `backlinks_unavailable` (the message carries the index status `updating` or
`unavailable`), `backlinks_auth_failed`, `backlinks_forbidden`, `backlinks_unreachable`,
`timeout`, `bad_response`, `backlinks_repo_mismatch`, `credential_unavailable`, `cursor_stale`.
A sidecar 401 triggers exactly one token refresh and one retry.

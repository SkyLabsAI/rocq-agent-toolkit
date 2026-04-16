# rocq-session

HTTP server that loads one Rocq `.v` file with `rocq-doc-manager` and exposes a
GET API for feedback at an LSP-style position (0-based line, UTF-16
`character`).

Three commands:

- `rocq-session-server path/to/file.v [--host HOST] [--port PORT] [--cwd DIR] [-- ROCQ_ARGS...]`
  — start the HTTP server.
- `rocq-session [--endpoint URL] SUBCOMMAND` — client for a running server.
- `rocq-session-cram-test file.v [command_json_args...]` — cram testing tool that executes session operations directly without server startup.
  - `rocq-session feedback LINE:CHAR` — GET `/feedback` (LSP-style 0-based
    line, UTF-16 character).
  - `rocq-session health` — GET `/health`.
  - `rocq-session cursor` — GET `/cursor` (current document cursor index).
  - `rocq-session query "QUERY." [--at LINE:CHAR]` — POST `/query`.
  - `rocq-session insert "COMMAND." [--at LINE:CHAR]` — POST `/insert`.
  - `rocq-session reload` — POST `/reload` (re-read the file from disk and
    reconcile the session).
  - `rocq-session quit` — POST `/quit` (asks the server to shut down).

Default client endpoint is `http://127.0.0.1:8765`.

Endpoints:

- `GET /health` — process up.
- `GET /cursor` — current document cursor index.
- `GET /feedback?line=LINE&character=CHAR` — LSP-style 0-based line and UTF-16
  character; returns JSON with `status` and `feedback_messages`.
- `POST /query` — run a Rocq query at an optional LSP position (`line` +
  `character`, 0-based UTF-16). If omitted, current cursor is used. If the
  computed location is before the current cursor, evaluation runs on a cloned +
  materialized cursor and does not move the live cursor.
- `POST /insert` — insert a command at an optional LSP position (`line` +
  `character`, 0-based UTF-16). If omitted, current cursor is used.
- `POST /reload` — re-read the file from disk, preserve the longest processed
  prefix that still matches the file, revert the cursor past any divergence,
  install the remaining file text as the new document suffix, and invalidate
  the affected cache entries. Returns counts of preserved / reverted items
  and kept / dropped cache entries.
- `POST /quit` — request a graceful shutdown (`202` + `{"status":
  "shutting_down"}` when wired up, `503` if not).

## Cram Testing

The `rocq-session-cram-test` tool provides a way to test session operations directly without starting an HTTP server. It loads a Rocq file using `rocq-doc-manager` and executes session commands specified as JSON arguments.

### Usage

```bash
rocq-session-cram-test file.v [command_json_args...]
```

Commands are specified as JSON strings:
- `"cursor"` - Get current cursor position
- `["query", {"text": "Check nat."}]` - Run a query
- `["insert", {"text": "Definition x := 0."}]` - Insert a command
- `["query", {"text": "Check x.", "line": 1, "character": 10}]` - Query at specific position

### Examples

```bash
# Basic operations
rocq-session-cram-test test.v \
  "cursor" \
  '["insert", {"text": "Definition x := 0."}]' \
  '["query", {"text": "Check x."}]' \
  "cursor"

# With specific positions
rocq-session-cram-test test.v \
  '["query", {"text": "About nat.", "line": 0, "character": 0}]' \
  '["insert", {"text": "Lemma test : True.", "line": 1, "character": 0}]'
```

### Output Format

Commands are echoed with their arguments, followed by results:

```
cursor({})
= {"status": "ok", "index": 0}
insert({"text": "Definition x := 0."})
= {"status": "ok", "index": 1, "command_data": {...}}
```

This format is suitable for cram tests and can be used to verify session operation behavior without the complexity of HTTP server setup.

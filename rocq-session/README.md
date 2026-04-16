# rocq-session

HTTP server that loads one Rocq `.v` file with `rocq-doc-manager` and exposes a
GET API for feedback at an LSP-style position (0-based line, UTF-16
`character`).

Two commands:

- `rocq-session-server path/to/file.v [--host HOST] [--port PORT] [--cwd DIR] [-- ROCQ_ARGS...]`
  — start the HTTP server.
- `rocq-session [--endpoint URL] SUBCOMMAND` — client for a running server.
  - `rocq-session feedback LINE:CHAR` — GET `/feedback` (LSP-style 0-based
    line, UTF-16 character).
  - `rocq-session health` — GET `/health`.
  - `rocq-session quit` — POST `/quit` (asks the server to shut down).

Default client endpoint is `http://127.0.0.1:8765`.

Endpoints:

- `GET /health` — process up.
- `GET /feedback?line=LINE&character=CHAR` — LSP-style 0-based line and UTF-16
  character; returns JSON with `status` and `feedback_messages`.
- `POST /quit` — request a graceful shutdown (`202` + `{"status":
  "shutting_down"}` when wired up, `503` if not).

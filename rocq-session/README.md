# rocq-session

HTTP server that loads one Rocq `.v` file with `rocq-doc-manager` and exposes a GET API for feedback at an LSP-style position (0-based line, UTF-16 `character`).

Run: `rocq-session path/to/file.v [--host HOST] [--port PORT] [-- ROCQ_ARGS...]`

Endpoints:

- `GET /health` — process up.
- `GET /feedback?line=LINE&character=CHAR` — LSP-style 0-based line and UTF-16 character; returns JSON with `status` and `feedback_messages`.

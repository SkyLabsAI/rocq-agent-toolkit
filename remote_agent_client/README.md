# Remote Agent

This agent acts as a client that connects to a remote server, allowing for distributed proof agent execution.

## Usage

Run the remote proof agent with `rocq-pipeline` runner args first, then pass **client-specific args at the end** after `--`:

```bash
uv run remote-proof-agent --task-file <path-to-task.yaml> -- --api-key-env OPENROUTER_API_KEY
```

Notes:

- Arguments **before** `--` are parsed by `rocq-pipeline` (task selection, output dir, jobs, etc.).
- Arguments **after** `--` are parsed by the remote agent client (server URL, provider, auth, etc.).

### Compulsory inputs

- **Task selection (required)**: you must provide exactly one of:
  - `--task-file <path>` (YAML/JSON task file), or
  - `--task-json <literal-json>`
- **LLM API key (required)**: the environment variable named by `--api-key-env` must be set and non-empty.
  - Default env var name is `OPENROUTER_API_KEY`.
- **GitHub auth (required)**: the client must obtain a GitHub token (it will resolve from env/cached token, otherwise it will prompt device-flow login).

### Runner options (before `--`)

Commonly used:

- `--task-file`: Path to the task file (YAML/JSON)
- `--task-json`: Task descriptor as literal JSON

### Remote client options (after `--`)

- `--server`: Remote agent server base URL (default: `http://localhost:8001`)
- `--remote-agent`: Server-side agent script name (default: `react-code-proof-agent`)
- `--remote-param`: KEY=JSON parameter passed to server-side agent (repeatable)
- `--provider`: LLM provider name for BYOK (default: `openrouter`)
- `--api-key-env`: Env var name containing the provider API key (default: `OPENROUTER_API_KEY`)
- `--github-login`: Force interactive GitHub device-flow login

### Example

```bash
uv run remote-proof-agent \
  --task-file ../rocq-pipeline/examples/tasks.yaml \
  -- \
  --server http://localhost:8001 \
  --remote-agent react-code-proof-agent \
  --api-key-env OPENROUTER_API_KEY
```

### GitHub authentication

The client requires a GitHub token and sends it as:

- `Authorization: Bearer <token>` during `POST /v1/session`

Token resolution:

- First: `GH_TOKEN` or `GITHUB_TOKEN`
- Then: cached token at `~/.config/rocq-agent-toolkit/github_token.json`
- Else: interactive device-flow login (uses a built-in OAuth `client_id`)

Optional:

- Set `RDM_GITHUB_OAUTH_CLIENT_ID` to override the built-in `client_id`.

## Architecture


1. Creates a session with a remote proof server via HTTP
2. Establishes a WebSocket connection for bidirectional communication
3. Forwards JSON-RPC requests from the server to the local Rocq document manager
4. Receives proof results from the remote agent

## Configuration

The agent is configured via `RemoteProofAgentConfig`:

- `server`: Base HTTP URL for session creation
- `remote_agent`: Server-side agent script name
- `remote_parameters`: Parameters passed to the remote agent
- `inference`: Optional BYOK/model selection
- `budget`: Budget controls enforced by the server
- `ping_interval_s`: WebSocket keepalive ping interval (default: 20s)
- `ping_timeout_s`: WebSocket keepalive timeout (default: 20s)


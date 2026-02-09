# Remote Agent

This agent acts as a client that connects to a remote server, allowing for distributed proof agent execution.

## Usage

Run the remote proof agent with:

```bash
uv run remote-proof-agent --task-file <path-to-task.yaml>
```

### Command Line Options

- `--server`: Remote agent server base URL (default: `http://localhost:8001`)
- `--remote-agent`: Server-side agent script name (default: `react-code-proof-agent`)
- `--remote-param`: KEY=JSON parameter passed to server-side agent (repeatable)
- `--task-file`: Path to the task file

### Example

```bash
remote-proof-agent \
  --server http://localhost:8001 \
  --remote-agent react-code-proof-agent \
  --task-file tasks/my-proof.yaml
```

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

## Development

The package structure:

```
src/remote_agent/
├── __init__.py       # Package exports
├── agent.py          # RemoteProofAgent implementation
├── builder.py        # AgentBuilder for CLI integration
├── cli.py            # Command-line entrypoint
└── config.py         # Configuration dataclass
```

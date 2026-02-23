# Remote Agent

This agent acts as a client that connects to a remote server to automatically complete Rocq proofs. It scans a .v file for Admitted theorems, invokes a remote agent to solve them, and replaces them with valid proof scripts.

## Usage

```bash
uv run rocq-remote-agent <path-to-file.v> -- <arguments-for-the-agent>
```

### Remote client options (after `--`)

- `--server`: Remote agent server base URL (default: `http://localhost:8001`)
- `--remote-agent`: Server-side agent script name (default: `react-code-proof-agent`)
- `--remote-param`: KEY=JSON parameter passed to server-side agent (repeatable)
- `--provider`: LLM provider name for BYOK (default: `openrouter`)
- `--api-key-env`: Env var name containing the provider API key (default: `OPENROUTER_API_KEY`)
- `--github-login`: Force interactive GitHub device-flow login


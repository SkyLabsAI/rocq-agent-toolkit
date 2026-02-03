## Remote Agent Client

This project contains the **public** client-side pieces for the Remote Agent setup:

- `remote_agent_client.protocol`: shared protocol models (Pydantic)
- `remote_agent_client.proxy_cli`: the proxy process that runs next to `rocq-doc-manager`

Server code lives in the private project `psi/backend/remote_agent_server`.

### Run the proxy

Create a session against a running server and connect the proxy:

```bash
uv run rocq-remote-rdm-proxy --server http://localhost:8001 --file path/to/file.v --agent react-code-proof-agent
```


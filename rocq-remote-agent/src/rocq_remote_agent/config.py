from __future__ import annotations

from dataclasses import dataclass, field

type JsonValue = object


@dataclass
class RemoteProofAgentConfig:
    # Base HTTP URL for session creation, e.g. "https://host:port"
    server: str = "https://agents.skylabs-ai.com"

    # Server-side agent script name (e.g. "react-code-proof-agent")
    remote_agent: str = "react-code-proof-agent"

    # Parameters passed to the remote agent.
    remote_parameters: dict[str, JsonValue] = field(default_factory=dict)

    # Optional BYOK/model selection passed through to the server.
    inference: dict[str, JsonValue] | None = None

    # GitHub auth token to present to the remote server.
    # This is sent as an HTTP `Authorization: Bearer ...` header during session creation.
    github_token: str | None = None

    # Budget controls enforced by the server.
    budget: dict[str, JsonValue] = field(default_factory=dict)

    # Websocket keepalive settings.
    ping_interval_s: int = 20
    ping_timeout_s: int = 20

    # RPC timeout budget enforced server-side; client uses websocket keepalive.

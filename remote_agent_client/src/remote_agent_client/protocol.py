from __future__ import annotations

import time
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field

PROTOCOL_VERSION: int = 1


class BudgetConfig(BaseModel):
    """Budget controls enforced by the server (upper bounds may apply)."""

    model_config = ConfigDict(extra="forbid")

    max_total_tokens: int | None = None
    max_llm_calls: int | None = None
    max_tool_calls: int | None = None
    max_wall_seconds: int | None = None


class InferenceConfig(BaseModel):
    """Bring-your-own-key (BYOK) + model selection for the agent.

    The server decides how (or whether) to honor these settings based on policy.
    """

    model_config = ConfigDict(extra="forbid")

    provider: str | None = None
    model: str | None = None
    base_url: str | None = None
    # NOTE: this is intentionally a plain string (not SecretStr) because
    # Pydantic masks SecretStr on serialization, which would break BYOK.
    # Never log this field.
    api_key: str | None = Field(default=None, repr=False)


class AgentConfig(BaseModel):
    """Request to run a server-side agent by name."""

    model_config = ConfigDict(extra="forbid")

    # Stable, server-defined identifier. For Brick agents this maps nicely to
    # brick_agents' `script_entrypoint` (e.g. "react-code-proof-agent").
    name: str
    parameters: dict[str, Any] = Field(default_factory=dict)
    inference: InferenceConfig | None = None
    budget: BudgetConfig = Field(default_factory=BudgetConfig)


class LocatorConfig(BaseModel):
    """Where in the document to start proving."""

    model_config = ConfigDict(extra="forbid")

    kind: Literal["admit"] = "admit"


class ProxyMeta(BaseModel):
    model_config = ConfigDict(extra="forbid")

    # Partner-side software info.
    client_version: str | None = None

    # Local document info (non-sensitive).
    file_path: str | None = None
    rocq_args: list[str] | None = None


class ProxyHello(BaseModel):
    """First message on the websocket (proxy -> server)."""

    model_config = ConfigDict(extra="forbid")

    type: Literal["hello"] = "hello"
    protocol_version: int = PROTOCOL_VERSION
    token: str
    agent: AgentConfig
    locator: LocatorConfig = Field(default_factory=LocatorConfig)
    meta: ProxyMeta = Field(default_factory=ProxyMeta)


class HelloAck(BaseModel):
    model_config = ConfigDict(extra="forbid")

    type: Literal["hello_ack"] = "hello_ack"
    protocol_version: int = PROTOCOL_VERSION
    session_id: str
    server_time_ms: int = Field(default_factory=lambda: int(time.time() * 1000))


class Event(BaseModel):
    """Server -> proxy progress/status updates."""

    model_config = ConfigDict(extra="forbid")

    type: Literal["event"] = "event"
    level: Literal["debug", "info", "warning", "error"] = "info"
    message: str
    data: dict[str, Any] | None = None
    time_ms: int = Field(default_factory=lambda: int(time.time() * 1000))


class Result(BaseModel):
    model_config = ConfigDict(extra="forbid")

    type: Literal["result"] = "result"
    session_id: str
    agent_name: str
    proof: list[str]
    summary: dict[str, Any] | None = None


class ErrorMsg(BaseModel):
    model_config = ConfigDict(extra="forbid")

    type: Literal["error"] = "error"
    session_id: str | None = None
    code: str
    message: str
    data: dict[str, Any] | None = None


class SessionInfo(BaseModel):
    model_config = ConfigDict(extra="forbid")

    session_id: str
    token: str
    ws_path: str
    ws_url: str


from __future__ import annotations

import argparse
import json
from typing import cast

from rocq_pipeline.agent.base import Agent, AgentBuilder

from .agent import RemoteProofAgent
from .config import RemoteProofAgentConfig

type JsonValue = object


def _parse_kv_json(raw: str) -> tuple[str, JsonValue]:
    if "=" not in raw:
        raise ValueError("expected KEY=JSON")
    k, v = raw.split("=", 1)
    return k.strip(), cast(JsonValue, json.loads(v))


class RemoteProofAgentBuilder(AgentBuilder):
    def __init__(self) -> None:
        super().__init__(agent_type=RemoteProofAgent)
        self._config = RemoteProofAgentConfig()

    def add_args(self, args: list[str]) -> None:
        p = argparse.ArgumentParser("RemoteProofAgent")
        p.add_argument(
            "--server",
            type=str,
            default=self._config.server,
            help="Remote agent server base URL (creates session via /v1/session)",
        )
        p.add_argument(
            "--remote-agent",
            type=str,
            default=self._config.remote_agent,
            help="Server-side agent script name (e.g. react-code-proof-agent)",
        )
        p.add_argument(
            "--remote-param",
            action="append",
            default=[],
            help=(
                "KEY=JSON parameter passed to server-side agent (repeatable)"
            ),
        )
        parsed, _unknown = p.parse_known_args(args)

        params: dict[str, JsonValue] = {}
        for item in parsed.remote_param:
            k, v = _parse_kv_json(item)
            params[k] = v

        self._config = RemoteProofAgentConfig(
            server=str(parsed.server),
            remote_agent=str(parsed.remote_agent),
            remote_parameters=params,
        )

    def __call__(self, prompt: str | None = None) -> Agent:
        return RemoteProofAgent(self._config)


# Convenient builder for rocq-pipeline `--agent brick_agents....:builder`
builder = RemoteProofAgentBuilder()

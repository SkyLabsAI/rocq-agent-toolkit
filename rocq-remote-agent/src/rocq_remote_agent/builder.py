from __future__ import annotations

import argparse
import json
import os
from typing import cast

from rocq_pipeline.agent.base import Agent, AgentBuilder

from .agent import RemoteAgent
from .config import RemoteProofAgentConfig
from .github_auth import (
    interactive_github_login_device_flow,
    resolve_github_token,
)

type JsonValue = object

_DEFAULT_GITHUB_OAUTH_CLIENT_ID = "Ov23liVZwVm5YXg4UQKk"


def _parse_kv_json(raw: str) -> tuple[str, JsonValue]:
    if "=" not in raw:
        raise ValueError("expected KEY=JSON")
    k, v = raw.split("=", 1)
    return k.strip(), cast(JsonValue, json.loads(v))


class RemoteAgentBuilder(AgentBuilder):
    def __init__(self) -> None:
        super().__init__(agent_type=RemoteAgent)
        self._config = RemoteProofAgentConfig()

    def add_args(self, args: list[str]) -> None:
        p = argparse.ArgumentParser("...agent arguments...")
        p.add_argument(
            "--server",
            type=str,
            default=self._config.server,
            help=("Remote agent server base URL"),
        )
        p.add_argument(
            "--remote-agent",
            type=str,
            default=self._config.remote_agent,
            help="Server-side agent script name",
        )
        p.add_argument(
            "--remote-param",
            action="append",
            default=[],
            help=("KEY=VALUE parameter passed to the server-side agent. "
                  "Specify multiple times for multiple params (e.g., "
                  "--remote-param max_llm_calls=25 --remote-param max_tool_calls=25)."),
        )
        p.add_argument(
            "--provider",
            type=str,
            default="openrouter",
            help="LLM provider name (e.g. openrouter).",
        )
        p.add_argument(
            "--api-key-env",
            type=str,
            default="OPENROUTER_API_KEY",
            help=(
                "Name of the environment variable containing the API Key. "
                "Defaults to 'OPENROUTER_API_KEY'."
            ),
        )
        p.add_argument(
            "--github-login",
            action="store_true",
            help=(
                "Force an interactive GitHub device-flow login "
                "(overrides cached token)."
            ),
        )
        parsed, _unknown = p.parse_known_args(args)

        params: dict[str, JsonValue] = {}
        for item in parsed.remote_param:
            k, v = _parse_kv_json(item)
            params[k] = v

        env_var_name = parsed.api_key_env
        api_key_value = os.environ.get(env_var_name)

        if not api_key_value:
            raise ValueError(
                f"RemoteProofAgent error: The environment variable '{env_var_name}' "
                "is not set or is empty. Please export it before running."
            )

        inference_config = {
            "provider": parsed.provider,
            "api_key": api_key_value,
        }

        # GitHub auth is required.
        # Token sources (in priority order):
        # - explicit env (`GH_TOKEN` / `GITHUB_TOKEN`)
        # - cached token file (~/.config/rocq-agent-toolkit/github_token.json)
        # - interactive device-flow login (requires `RDM_GITHUB_OAUTH_CLIENT_ID`)
        github_token: str | None
        if parsed.github_login:
            github_token = None
        else:
            github_token = resolve_github_token(
                token_env_names=["GH_TOKEN", "GITHUB_TOKEN"],
            )

        if not github_token:
            # Device flow OAuth `client_id` is intentionally non-secret and safe
            # to ship in public client code. Allow env override for flexibility.
            client_id = os.environ.get(
                "RDM_GITHUB_OAUTH_CLIENT_ID",
                _DEFAULT_GITHUB_OAUTH_CLIENT_ID,
            ).strip()
            github_token = interactive_github_login_device_flow(
                client_id=client_id,
                scope="read:user",
            )

        self._config = RemoteProofAgentConfig(
            server=str(parsed.server),
            remote_agent=str(parsed.remote_agent),
            remote_parameters=params,
            inference=inference_config,
            github_token=github_token,
        )

    def __call__(self, prompt: str | None = None) -> Agent:
        return RemoteAgent(self._config)


# Convenient builder for rocq-pipeline `--agent brick_agents....:builder`
builder = RemoteAgentBuilder()

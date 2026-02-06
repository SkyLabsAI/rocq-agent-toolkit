from __future__ import annotations as _annotations

import argparse
from typing import override

import rocq_pipeline
import rocq_pipeline.task_runner as RAT
from pydantic_ai import Agent
from pydantic_ai.models import Model
from pydantic_ai.models.openai import OpenAIChatModel
from pydantic_ai.providers import Provider
from pydantic_ai.providers.openai import OpenAIProvider
from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_pipeline.agent import AgentBuilder, ProofAgent, TaskResult
from rocq_pipeline.args_util import validate_url

from rocq_agent_tools_pydantic.tools import RocqCursorDeps, rocq_cursor_toolset


def format_goal(pfs: rdm_api.ProofState) -> str:
    return "\n\n".join(pfs.focused_goals)


class ToolAgent(ProofAgent):
    def __init__(self, model: Model, *, prompt: str | None = None):
        self._prompt = prompt
        self._agent = Agent(
            model,
            system_prompt="You are an expert in verification using the Rocq proof assistant.",
            deps_type=RocqCursorDeps,
            retries=2,
        )

    async def prove(self, rc: RocqCursor) -> TaskResult:
        deps = RocqCursorDeps(rc)
        goal = rc.current_goal()
        if goal is None:
            return self.finished(rc)

        prompt_lines = [
            "Prove this Rocq theorem using the provided tools. Use the `current_goals` tool to get the current goal. To check whether your proof is complete, use the `qed` command.",
            "",
            "The theorem to prove is:",
            "",
            format_goal(goal),
        ]
        if self._prompt:
            prompt_lines.extend(["", self._prompt])

        agent_result = await self._agent.run(
            prompt_lines,
            deps=deps,
            toolsets=[rocq_cursor_toolset],
        )

        # Check whether the proof is complete.
        # When we are doing something like filling and `admit`, `Qed` will not work.
        # Ideally, the RocqCursor would contain the necessary information
        result = rc.insert_command("Qed.")
        if isinstance(result, rdm_api.Err):
            return self.give_up(rc, agent_result.response.text or "Agent gave up")
        return self.finished(rc)


class ToolAgentBuilder(AgentBuilder):
    # This is the default url for LLMStudio
    _provider: Provider = OpenAIProvider(base_url="http://localhost:1234/v1")
    _model: Model = OpenAIChatModel("mistralai/ministral-3-3b", provider=_provider)

    @override
    def add_args(self, args: list[str]) -> None:
        # 1. Initialize the parser
        parser = argparse.ArgumentParser(
            description="A script to process a base URL and a model name."
        )

        parser.add_argument(
            "--base-url",
            type=validate_url,
            help="The base URL for the API (e.g., http://localhost:1234/v1)",
            default="http://localhost:1234/v1",
        )
        parser.add_argument(
            "--model",
            type=str,
            help="The name of the model to use (e.g., 'mistralai/ministral-3-3b' or 'openai/gpt-oss-20b')",
            default="openai/gpt-oss-20b",
        )
        parser.add_argument(
            "--key", type=str, help="The key to access the model, if any", default=None
        )

        ns = parser.parse_args(args)
        self._provider = OpenAIProvider(
            base_url=ns.base_url, api_key=ns.key if ns.key else None
        )
        self._model = OpenAIChatModel(ns.model, provider=self._provider)

    @override
    def __call__(self, prompt: str | None = None) -> rocq_pipeline.agent.Agent:
        return ToolAgent(self._model, prompt=prompt)


builder = ToolAgentBuilder()


def rat_main() -> bool:
    return RAT.agent_main(builder)

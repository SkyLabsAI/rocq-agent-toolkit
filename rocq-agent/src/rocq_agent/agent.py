from __future__ import annotations as _annotations

import asyncio
import os
from pathlib import Path

import rocq_pipeline.task_runner as RAT

# import logfire
from pydantic_ai import Agent
from pydantic_ai.models.openai import OpenAIChatModel
from pydantic_ai.providers.openai import OpenAIProvider
from rocq_doc_manager import DuneUtil, RocqCursor, RocqDocManager
from rocq_pipeline.agent import AgentBuilder, ProofAgent, TaskResult
from rocq_pipeline.locator import FirstLemma

from rocq_agent.tools import RocqCursorDeps, rocq_cursor_toolset

# 'if-token-present' means nothing will be sent (and the example will work) if you don't have logfire configured
# logfire.configure(send_to_logfire="if-token-present")
# logfire.instrument_pydantic_ai()


def format_goal(pfs: RocqCursor.ProofState) -> str:
    return "\n\n".join(pfs.focused_goals)


LOCAL = True
if LOCAL:
    provider = OpenAIProvider(base_url="http://localhost:1234/v1")
    # model = OpenAIChatModel("openai/gpt-oss-20b", provider=provider)
    model = OpenAIChatModel("mistralai/ministral-3-3b", provider=provider)
else:
    provider = OpenAIProvider(
        base_url="http://172.31.0.1:8770/v1", api_key=os.environ["VLLM_API_KEY"]
    )
    model = OpenAIChatModel("gpt-4o-mini", provider=provider)


class ToolAgent(ProofAgent):
    def __init__(self, model, *, prompt: str | None = None):
        if prompt is None:
            prompt = (
                """You are an expert in verification using the Rocq proof assistant."""
            )
        self._agent = Agent(model, instructions="", deps_type=RocqCursorDeps, retries=2)

    async def prove(self, rc: RocqCursor) -> TaskResult:
        deps = RocqCursorDeps(rc)
        goal = rc.current_goal()
        if goal is None:
            return self.finished(rc)

        agent_result = await self._agent.run(
            f"""Prove this Rocq theorem using the provided tools. Use the `current_goal` tool to get the current goal. To check whether your proof is complete, use the `qed` command.

            The theorem to prove is:
               {format_goal(goal)}""",
            deps=deps,
            toolsets=[rocq_cursor_toolset],
        )

        # Check whether the proof is complete.
        # When we are doing something like filling and `admit`, `Qed` will not work.
        # Ideally, the RocqCursor would contain the necessary information
        result = rc.insert_command("Qed.")
        if isinstance(result, RocqCursor.Err):
            return self.give_up(rc, agent_result.response.text or "Agent gave up")
        return self.finished(rc)


builder = AgentBuilder.of_agent(ToolAgent)


async def amain() -> None:
    file = (
        Path(__file__).parent.parent.parent.parent
        / "rocq-pipeline"
        / "examples"
        / "theories"
        / "my_nat.v"
    )

    loc = FirstLemma(lemma_name="zero_add")
    with RocqDocManager(
        DuneUtil.rocq_args_for("my_nat.v", cwd=file.parent),
        file_path=str(file),
        dune=True,
    ).sess(load_file=True) as rdm:
        rc = rdm.cursor()
        if not loc(rc):
            print("failed to locate lemma")
            return
        agent = builder()
        start_prefix = rc.doc_prefix()
        result: TaskResult = await agent.run(rc)
        if result.success:
            print("Proved!")
            end_prefix = rc.doc_prefix()
            if start_prefix == end_prefix[0 : len(start_prefix)]:
                script = "\n  ".join(
                    [
                        entry.text
                        for entry in end_prefix[len(start_prefix) :]
                        if entry.kind == "command"
                    ]
                )
                print(f"Final proof script:\n  {script}")
            else:
                print("Warning: Cursor does not extend initial cursor.")
        else:
            print("Failed to prove theorem")


def main() -> None:
    asyncio.run(amain())


def rat_main() -> bool:
    return RAT.agent_main(AgentBuilder.of_agent(ToolAgent))

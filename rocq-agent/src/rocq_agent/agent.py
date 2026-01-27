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

from rocq_agent.tools import Deps, rocq_cursor_toolset

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


AGENT = Agent(
    model,
    # 'Be concise, reply with one sentence.' is enough for some models (like openai) to use
    # the below tools appropriately, but others like anthropic and gemini require a bit more direction.
    instructions="You are a Rocq and Coq expert.",
    deps_type=Deps,
    retries=2,
)


class ToolAgent(ProofAgent):
    def prove(self, rc: RocqCursor) -> TaskResult:
        deps = Deps(rocq_cursor=rc, rocq_start=len(rc.doc_prefix()))
        goal = rc.current_goal()
        if goal is None:
            return self.finished(rc)

        agent_result = AGENT.run_sync(
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
            return super().give_up(rc, agent_result.response.text or "Agent gave up")
        return super().finished(rc)


async def amain():
    file = (
        Path(__file__).parent.parent.parent.parent
        / "rocq-pipeline"
        / "examples"
        / "theories"
        / "my_nat.v"
    )
    # for toolset in AGENT.toolsets:
    #     print(dir(toolset))
    #     for nm, _ in toolset.tools.items():
    #         print(nm)

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
        prefix = rc.doc_prefix()
        # logfire.instrument_httpx(client, capture_all=True)
        deps = Deps(rocq_cursor=rc, rocq_start=len(rc.doc_prefix()))
        result = await AGENT.run(
            f"""Prove this Rocq theorem using the provided tools. Use the `current_goal` tool to get the current goal. To check whether your proof is complete, use the `qed` command.

            The theorem to prove is:
               {format_goal(rc.current_goal())}""",
            deps=deps,
        )

        for message in result.new_messages():
            print("-" * 20)
            # The 'role' will be 'user', 'model' (agent), or 'tool'
            print(f"Role: {message.kind}")
            print(f"Content: {message}")

        final_prefix = rc.doc_prefix()
        proof = [cmd.text for cmd in final_prefix[len(prefix) :]]
        print("Response:", result.output)
        print(f"Proof\n {'\n '.join(proof)}")


def main():
    asyncio.run(amain())


def rat_main():
    return RAT.agent_main(AgentBuilder.of_agent(ToolAgent))

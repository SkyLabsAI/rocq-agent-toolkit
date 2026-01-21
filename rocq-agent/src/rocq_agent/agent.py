from __future__ import annotations as _annotations

import asyncio
import os
from dataclasses import dataclass
from pathlib import Path

import rocq_pipeline.task_runner as RAT

# import logfire
from pydantic import BaseModel
from pydantic_ai import Agent, FunctionToolset, RunContext
from pydantic_ai.models.openai import OpenAIChatModel
from pydantic_ai.providers.openai import OpenAIProvider
from rocq_doc_manager import DuneUtil, RocqCursor, RocqDocManager, rocq_cursor
from rocq_pipeline import AgentBuilder
from rocq_pipeline.agent import ProofAgent, TaskResult
from rocq_pipeline.locator import FirstLemma

# 'if-token-present' means nothing will be sent (and the example will work) if you don't have logfire configured
# logfire.configure(send_to_logfire="if-token-present")
# logfire.instrument_pydantic_ai()


def format_goal(pfs: RocqCursor.ProofState) -> str:
    return "\n\n".join(pfs.focused_goals)


@dataclass
class Deps:
    rocq_cursor: RocqCursor
    rocq_start: int


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


class RocqResult(BaseModel):
    error: str | None
    goal: list[str] | None


AGENT = Agent(
    model,
    # 'Be concise, reply with one sentence.' is enough for some models (like openai) to use
    # the below tools appropriately, but others like anthropic and gemini require a bit more direction.
    instructions="You are a Rocq and Coq expert.",
    deps_type=Deps,
    retries=2,
)


@AGENT.tool
async def current_goal(ctx: RunContext[Deps]) -> list[str] | None:
    """Get the focused goals."""
    result = ctx.deps.rocq_cursor.current_goal()
    print(result)
    if result is None:
        return None
    return result.focused_goals


@AGENT.tool
async def run_tactic(ctx: RunContext[Deps], tactic: str) -> RocqResult:
    """Run a tactic on the current goal.

    Args:
        tactic: The Rocq tactic to run. It should end with a ., e.g. 'intros.'
    """
    print(f"run_tactic: '{tactic}'")
    if tactic[-1] == ".":
        itactic = tactic[:-1]
    else:
        itactic = tactic
    result = ctx.deps.rocq_cursor.query(f"progress ({itactic}).")
    if isinstance(result, RocqCursor.Err):
        return RocqResult(error=result.message, goal=None)
    else:
        assert isinstance(result, RocqCursor.CommandData)
        result = ctx.deps.rocq_cursor.insert_command(tactic)
        assert isinstance(result, RocqCursor.CommandData)
        if result.proof_state:
            return RocqResult(error=None, goal=result.proof_state.focused_goals)
        else:
            return RocqResult(error=None, goal=[])


@AGENT.tool
async def run_query(ctx: RunContext[Deps], tactic: str) -> RocqResult:
    """Run the Rocq query.

    Args:
        tactic: The Rocq query to run. It should end with a ., e.g. 'Search nat.'
    """
    print(f"run_tactic: '{tactic}'")
    if tactic[-1] == ".":
        itactic = tactic[:-1]
    else:
        itactic = tactic
    result = ctx.deps.rocq_cursor.query(f"progress ({itactic}).")
    if isinstance(result, RocqCursor.Err):
        return RocqResult(error=result.message, goal=None)
    else:
        assert isinstance(result, RocqCursor.CommandData)
        result = ctx.deps.rocq_cursor.insert_command(tactic)
        assert isinstance(result, RocqCursor.CommandData)
        if result.proof_state:
            return RocqResult(error=None, goal=result.proof_state.focused_goals)
        else:
            return RocqResult(error=None, goal=[])


@AGENT.tool
async def proof_script(ctx: RunContext[Deps]) -> list[str]:
    """Returns the current tactics in the proof."""
    prefix = ctx.deps.rocq_cursor.doc_prefix()[ctx.deps.rocq_start :]
    return [cmd.text for cmd in prefix if cmd.kind == "command"]


@AGENT.tool
async def backtrack(ctx: RunContext[Deps], count: int) -> bool:
    """Backtrack before the last several commands within the proof.

    Args:
        count: The number of commands to revert.
    Returns:
        True if the revert succeeded, False otherwise
    """
    print(f"revert {count}")
    start = ctx.deps.rocq_start
    current_index = ctx.deps.rocq_cursor.cursor_index()
    if count > current_index - start:
        return False
    ctx.deps.rocq_cursor.revert_before(erase=True, index=current_index - count)
    return True


@AGENT.tool
def qed(ctx: RunContext[Deps]) -> bool:
    """Finish the current proof.

    Returns false if the proof can not be completed as this point.
    """
    print("qed")
    result = ctx.deps.rocq_cursor.query("Qed.")
    return not isinstance(result, RocqCursor.Err)


# rocq_cursor_toolset = FunctionToolset(
#     [current_goal, run_tactic, proof_script, backtrack, qed]
# )


class ToolAgent(ProofAgent):
    def prove(self, rc: RocqCursor) -> TaskResult:
        deps = Deps(rocq_cursor=rc, rocq_start=len(rc.doc_prefix()))

        result = AGENT.run_sync(
            f"""Prove this Rocq theorem using the provided tools. Use the `current_goal` tool to get the current goal. To check whether your proof is complete, use the `qed` command.

            The theorem to prove is:
               {format_goal(rc.current_goal())}""",
            deps=deps,
            tools=[qed, current_goal],
            # toolsets=[rocq_cursor_toolset],
        )
        for message in result.new_messages():
            print("-" * 20)
            # The 'role' will be 'user', 'model' (agent), or 'tool'
            print(f"Role: {message.kind}")
            print(f"Content: {message}")

        # Check whether the proof is complete
        result = rc.insert_command("Qed.")
        if isinstance(result, RocqCursor.Err):
            return super().give_up(rc, "Failed to find a proof")
        return super().finished(rc)


async def amain():
    file = (
        Path(__file__).parent.parent.parent.parent
        / "rocq-pipeline"
        / "examples"
        / "theories"
        / "my_nat.v"
    )
    for toolset in AGENT.toolsets:
        print(dir(toolset))
        for nm, _ in toolset.tools.items():
            print(nm)

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

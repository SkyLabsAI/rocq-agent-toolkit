from pydantic import BaseModel
from pydantic.dataclasses import dataclass
from pydantic_ai.tools import RunContext
from pydantic_ai.toolsets import FunctionToolset
from pydantic_ai.toolsets.abstract import AbstractToolset
from rocq_doc_manager.rocq_cursor import RocqCursor


class RocqResult[T](BaseModel):
    error: str | None
    result: T | None


@dataclass
class Deps:
    rocq_cursor: RocqCursor
    rocq_start: int


async def current_goal(ctx: RunContext[Deps]) -> list[str] | None:
    """Get the focused goals."""
    result = ctx.deps.rocq_cursor.current_goal()
    print(result)
    if result is None:
        return None
    return result.focused_goals


async def run_tactic(ctx: RunContext[Deps], tactic: str) -> RocqResult[list[str]]:
    """Run a tactic on the current goal.

    Args:
        tactic: The Rocq tactic to run. It should end with a ., e.g. 'intros.'
    """
    if tactic[-1] == ".":
        itactic = tactic[:-1]
    else:
        itactic = tactic
    result = ctx.deps.rocq_cursor.query(f"progress ({itactic}).")
    if isinstance(result, RocqCursor.Err):
        return RocqResult(error=result.message, result=None)
    else:
        assert isinstance(result, RocqCursor.CommandData)
        cresult = ctx.deps.rocq_cursor.insert_command(tactic)
        assert isinstance(cresult, RocqCursor.CommandData)
        if cresult.proof_state:
            return RocqResult(error=None, result=cresult.proof_state.focused_goals)
        else:
            return RocqResult(error=None, result=[])


async def run_query(ctx: RunContext[Deps], command: str) -> RocqResult[list[str]]:
    """Run the Rocq query, the results will not be added to the document.
    Only use this to run the commands `Search`, `Check`, `Print`, and `About`.

    Args:
        command: The Rocq query to run. It should end with a `.`, e.g. 'Search nat.'
    """
    if not any(command.startswith(x) for x in ["Search", "Check", "Print", "About"]):
        return RocqResult(
            error="Must be a query using `Search`, `Check`, `Print`, or `About`.",
            result=None,
        )
    result = ctx.deps.rocq_cursor.query(command)
    if isinstance(result, RocqCursor.Err):
        return RocqResult(error=result.message, result=None)
    else:
        return RocqResult(
            error=None, result=[fm.text for fm in result.feedback_messages]
        )


async def proof_script(ctx: RunContext[Deps]) -> list[str]:
    """Returns the current tactics in the proof."""
    prefix = ctx.deps.rocq_cursor.doc_prefix()[ctx.deps.rocq_start :]
    return [cmd.text for cmd in prefix if cmd.kind == "command"]


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


def qed(ctx: RunContext[Deps]) -> bool:
    """Finish the current proof.

    Returns false if the proof can not be completed as this point.
    """
    print("qed")
    result = ctx.deps.rocq_cursor.query("Qed.")
    return not isinstance(result, RocqCursor.Err)


rocq_cursor_toolset: AbstractToolset[Deps] = FunctionToolset(
    [current_goal, run_tactic, proof_script, backtrack, qed]
)

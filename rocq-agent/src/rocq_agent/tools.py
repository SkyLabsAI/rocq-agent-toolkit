from pydantic import BaseModel, Field
from pydantic_ai.tools import RunContext
from pydantic_ai.toolsets import FunctionToolset
from pydantic_ai.toolsets.abstract import AbstractToolset
from rocq_doc_manager.rocq_cursor import RocqCursor


class RocqResult[T](BaseModel):
    """The type used to communicate results from Rocq."""

    error: str | None = Field(
        description="None on success, or the error string if an error occurs"
    )
    result: T | None = Field(description="The result of the action")


class RocqCursorDeps:
    """The context information used to interact with Rocq."""

    rocq_cursor: RocqCursor
    rocq_script: list[tuple[int, str]]  # the cursor index and the command

    def __init__(self, rc: RocqCursor) -> None:
        self.rocq_cursor = rc
        self.rocq_script = []


async def current_goals(ctx: RunContext[RocqCursorDeps]) -> list[str] | None:
    """Get the focused goals."""
    result = ctx.deps.rocq_cursor.current_goal()
    if result is None:
        return None
    return result.focused_goals


async def run_tactic(
    ctx: RunContext[RocqCursorDeps], tactic: str
) -> RocqResult[list[str]]:
    """Run a tactic on the current goal.

    Args:
        tactic: The Rocq tactic to run. It should end with a ., e.g. 'intros.'

    Return:
        The result field will contain the new Rocq goals after the tactic runs.
    """
    result = ctx.deps.rocq_cursor.query(tactic)
    if isinstance(result, RocqCursor.Err):
        return RocqResult(error=result.message, result=None)
    else:
        assert isinstance(result, RocqCursor.CommandData)
        idx = ctx.deps.rocq_cursor.cursor_index()
        cresult = ctx.deps.rocq_cursor.insert_command(tactic)
        ctx.deps.rocq_script.append((idx, tactic))
        assert isinstance(cresult, RocqCursor.CommandData)
        if cresult.proof_state:
            return RocqResult(error=None, result=cresult.proof_state.focused_goals)
        else:
            return RocqResult(error=None, result=[])


async def run_query(
    ctx: RunContext[RocqCursorDeps], command: str
) -> RocqResult[list[str]]:
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


async def proof_script(ctx: RunContext[RocqCursorDeps]) -> list[str]:
    """Returns the current tactics in the proof."""
    return [cmd for _, cmd in ctx.deps.rocq_script]


async def backtrack(ctx: RunContext[RocqCursorDeps], count: int) -> bool:
    """Backtrack before the last several commands within the proof.

    Args:
        count: The number of commands to revert.
    Returns:
        True if the revert succeeded, False otherwise
    """
    if count > len(ctx.deps.rocq_script):
        return False

    idx, _ = ctx.deps.rocq_script[-count]

    ctx.deps.rocq_cursor.revert_before(erase=True, index=idx)
    ctx.deps.rocq_script = ctx.deps.rocq_script[:-count]
    return True


def qed(ctx: RunContext[RocqCursorDeps]) -> bool:
    """Finish the current proof.

    Returns false if the proof can not be completed as this point.
    """
    result = ctx.deps.rocq_cursor.query("Qed.")
    return not isinstance(result, RocqCursor.Err)


rocq_cursor_toolset: AbstractToolset[RocqCursorDeps] = FunctionToolset(
    [current_goals, run_tactic, proof_script, backtrack, qed]
)

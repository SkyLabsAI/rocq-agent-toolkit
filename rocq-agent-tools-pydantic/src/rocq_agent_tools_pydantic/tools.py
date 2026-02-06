from pydantic import BaseModel, Field
from pydantic_ai.tools import RunContext
from pydantic_ai.toolsets import FunctionToolset
from pydantic_ai.toolsets.abstract import AbstractToolset
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_doc_manager.rocq_cursor import RocqCursor


class RocqResult[T](BaseModel):
    """The type used to communicate Rocq results."""

    error: str | None = Field(
        description="None on success, or the error string if an error occurs"
    )
    result: T | None = Field(description="The result of the action")


class RocqProofStateDeps:
    """The context information used to interact with a **single Rocq proof state**.
    Specfically, agents can not use these tools to manipulate the document outside
    of the scope of the target theorem.

    These tools might be generalized in the future to provide different
    interaction paradigms.
    """

    rocq_cursor: RocqCursor
    rocq_script: list[tuple[int, str]]  # the cursor index and the command

    def __init__(self, rc: RocqCursor) -> None:
        self.rocq_cursor = rc
        self.rocq_script = []


async def current_goals(ctx: RunContext[RocqProofStateDeps]) -> list[str] | None:
    """Get the focused goals."""
    result = ctx.deps.rocq_cursor.current_goal()
    if result is None:
        return None
    return result.focused_goals


async def run_tactic(
    ctx: RunContext[RocqProofStateDeps], tactic: str
) -> RocqResult[list[str]]:
    """Run a tactic on the current goal.

    Args:
        tactic: The Rocq tactic to run. It should end with a ., e.g. 'intros.'

    Return:
        The result field will contain the new Rocq goals after the tactic runs.
    """
    idx = ctx.deps.rocq_cursor.cursor_index()
    result = ctx.deps.rocq_cursor.insert_command(tactic)
    if isinstance(result, rdm_api.Err):
        return RocqResult(error=result.message, result=None)
    else:
        assert isinstance(result, rdm_api.CommandData)
        ctx.deps.rocq_script.append((idx, tactic))
        if result.proof_state:
            return RocqResult(error=None, result=result.proof_state.focused_goals)
        else:
            return RocqResult(error=None, result=[])


async def run_query(
    ctx: RunContext[RocqProofStateDeps], command: str
) -> RocqResult[list[str]]:
    """Run the Rocq query, the results will not be added to the document.
    Only use this to run the commands `Search`, `Check`, `Print`, and `About`.

    Args:
        command: The Rocq query to run. It should end with a `.`, e.g. 'Search nat.'
    """
    command = command.strip()
    if not any(command.startswith(x) for x in ["Search", "Check", "Print", "About"]):
        return RocqResult(
            error="Query must start with one of `Search`, `Check`, `Print`, or `About`.",
            result=None,
        )
    result = ctx.deps.rocq_cursor.query(command)
    if isinstance(result, rdm_api.Err):
        return RocqResult(error=result.message, result=None)
    else:
        return RocqResult(
            error=None, result=[fm.text for fm in result.feedback_messages]
        )


async def proof_script(ctx: RunContext[RocqProofStateDeps]) -> list[str]:
    """Returns the current tactics in the proof."""
    return [cmd for _, cmd in ctx.deps.rocq_script]


async def backtrack(ctx: RunContext[RocqProofStateDeps], count: int) -> bool:
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


def qed(ctx: RunContext[RocqProofStateDeps]) -> bool:
    """Finish the current proof.

    Returns false if the proof can not be completed as this point.
    """
    # NOTE: Using `Qed` here prevents this from being used to prove single goals within
    # a larger proof.
    result = ctx.deps.rocq_cursor.query("Qed.")
    return not isinstance(result, rdm_api.Err)


rocq_cursor_toolset: AbstractToolset[RocqProofStateDeps] = FunctionToolset(
    [current_goals, run_tactic, proof_script, backtrack, qed]
)

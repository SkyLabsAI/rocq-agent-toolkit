from collections.abc import Callable

from pydantic import BaseModel, Field
from pydantic_ai.tools import RunContext
from pydantic_ai.toolsets import FunctionToolset
from pydantic_ai.toolsets.abstract import AbstractToolset
from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api


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
    result = await ctx.deps.rocq_cursor.current_goal()
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
    idx = await ctx.deps.rocq_cursor.cursor_index()
    result = await ctx.deps.rocq_cursor.insert_command(tactic)
    if isinstance(result, rdm_api.Err):
        return RocqResult(error=result.message, result=None)
    else:
        assert isinstance(result, rdm_api.CommandData)
        ctx.deps.rocq_script.append((idx, tactic))
        # NOTE: This is not really necessary.
        await ctx.deps.rocq_cursor.insert_blanks("\n")
        if result.proof_state:
            return RocqResult(error=None, result=result.proof_state.focused_goals)
        else:
            return RocqResult(error=None, result=[])


async def insert_tactics(
    ctx: RunContext[RocqProofStateDeps], text: str
) -> RocqResult[tuple[int, str | None, list[str] | None]]:
    """Inserts the given chunk of Rocq text (containing an arbitrary number of
    commands) into the proof. If an error occurs, all commands that could be
    run successfully are kept, and the remaining unprocessed text is returned
    together with the number of commands that were successfully processed.

    Args:
        text: The chunk of Rocq code to insert

    Return:
        The result field will contain a tuple giving:
        - the number of commands that were successfully run
        - any potential left-over text that could not be processed
        - the goals after the last successfully run command (if any)
    """
    sentences_or_err = await ctx.deps.rocq_cursor.split_sentences(text)
    error: str | None = None
    rest: str | None = None
    count = 0
    if isinstance(sentences_or_err, list):
        sentences = sentences_or_err
    else:
        sentences = sentences_or_err.data.sentences
        error = sentences_or_err.message
        rest = sentences_or_err.data.rest

    last_goals: list[str] | None = None
    for i, sentence in enumerate(sentences):
        if sentence.kind == "blanks":
            await ctx.deps.rocq_cursor.insert_blanks(sentence.text)
        else:
            result = await run_tactic(ctx, sentence.text)
            if result.error is None:
                last_goals = result.result
                count += 1
            else:
                rest = "".join([s.text for s in sentences[i:]]) + (
                    "" if rest is None else rest
                )
                return RocqResult(error=result.error, result=(count, rest, last_goals))

    return RocqResult(error=error, result=(count, rest, last_goals))


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
    result = await ctx.deps.rocq_cursor.query(command)
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
    if count == 0:
        return True
    elif count < 0 or count > len(ctx.deps.rocq_script):
        return False

    idx, _ = ctx.deps.rocq_script[-count]

    await ctx.deps.rocq_cursor.revert_before(erase=True, index=idx)
    ctx.deps.rocq_script = ctx.deps.rocq_script[:-count]
    return True


async def qed(ctx: RunContext[RocqProofStateDeps]) -> bool:
    """Finish the current proof.

    Returns false if the proof can not be completed as this point.
    """
    # NOTE: Using `Qed` here prevents this from being used to prove single goals within
    # a larger proof.
    result = await ctx.deps.rocq_cursor.query("Qed.")
    return not isinstance(result, rdm_api.Err)


rocq_cursor_toolset: AbstractToolset[RocqProofStateDeps] = FunctionToolset(
    [current_goals, run_tactic, proof_script, backtrack, qed], sequential=True
)

all_tools: list[Callable] = [
    current_goals,
    run_tactic,
    insert_tactics,
    run_query,
    proof_script,
    backtrack,
    qed,
]

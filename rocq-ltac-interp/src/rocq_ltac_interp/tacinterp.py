import json
from collections.abc import Sequence
from contextlib import AbstractAsyncContextManager
from types import TracebackType
from typing import Protocol, cast

from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_dune_util import DuneRocqPlugin

type LocalProofState = rdm_api.ProofState
type RunCommandResult = LocalProofState | None | rdm_api.Err


def diff_goals(
    pre: rdm_api.ProofState, on: int, post: rdm_api.ProofState | None
) -> LocalProofState | None:
    """Compute the relativized proof state for a tactic that runs on goal `on`."""
    if post is None:
        assert on == 0
        assert len(pre.focused_goals) == 1
        return None
    else:
        # the beginning and ending of the focused_goals will be the
        # same, but we need to compute the goals that change.
        assert pre.focused_goals[0:on] == post.focused_goals[0:on]
        preserved_end = len(pre.focused_goals) - on - 1
        fg = (
            post.focused_goals[on:]
            if preserved_end == 0
            else post.focused_goals[on:-preserved_end]
        )
        return rdm_api.ProofState(
            focused_goals=fg,
            unfocused_goals=post.unfocused_goals,
            shelved_goals=post.shelved_goals,
            given_up_goals=post.given_up_goals,
        )


class TacticRunner(Protocol):
    """Protocol for evaluating tactics."""

    async def __call__(
        self,
        rc: RocqCursor,
        goal: int,
        tac: str,
        *,
        pre: rdm_api.ProofState,
        trace: int | None = None,
    ) -> RunCommandResult:
        """This function **must** return a relativized ProofState.
        A relativized proof state can be computed using `diff_goals`.
        Clients that want to override this can implement `global_call`
        to get the
        """
        result = await rc.run_command(f"{goal}: {tac}.")
        if result is None:
            return result
        elif isinstance(result, rdm_api.Err):
            return result
        else:
            return diff_goals(pre, goal, result.proof_state)


class LtacThunk(Protocol):
    async def __call__(
        self,
        rc: RocqCursor,
        goal: int,
        *,
        pre: rdm_api.ProofState,
        trace: int | None = None,
    ) -> RunCommandResult: ...


def atomic_to_thunk(runner: TacticRunner, tactic: str) -> LtacThunk:
    async def result(
        rc: RocqCursor, goal: int, *, pre: rdm_api.ProofState, trace: int | None = None
    ) -> RunCommandResult:
        nonlocal runner
        nonlocal tactic
        return await runner.__call__(rc, goal, tactic, pre=pre, trace=trace)

    return result


PLUGIN = DuneRocqPlugin(
    opam_pkg="rocq-tactic-info", entry_points=["theories/explain.v"]
)


async def load(rc: RocqCursor) -> None:
    """Load the plugin.

    You must pass `PLUGIN` to the plugins."""
    if not isinstance(
        await rc.run_command("Require Import skylabs.tactic_info.explain."),
        rdm_api.CommandData,
    ):
        raise Exception("Failed to load module.")


type TacticAST = list[str | TacticAST]


async def copy_extension(*, src: RocqCursor, dst: RocqCursor) -> None:
    # copy the contents from self._cloned to self._cursor
    start_prefix = await dst.doc_prefix()
    end_prefix = await src.doc_prefix()
    assert end_prefix[0 : len(start_prefix)] == start_prefix
    for i in end_prefix[len(start_prefix) :]:
        if i.kind == "blanks":
            await dst.insert_blanks(i.text)
        else:
            assert isinstance(
                await dst.insert_command(i.text, ghost=i.kind == "ghost", blanks=None),
                rdm_api.CommandData,
            )


class LtacFail(Exception):
    """The Ltac failed.

    Note: This does not support n-level failure, e.g. `fail 2`."""

    pass


class LtacTry(AbstractAsyncContextManager):
    """Context manager that reverts effects if Ltac fails."""

    def __init__(self, rc: RocqCursor) -> None:
        self._cursor = rc
        self._cloned: None | RocqCursor = None

    async def __aenter__(self) -> RocqCursor:
        self._cloned = await self._cursor.clone()
        return self._cloned

    async def __aexit__(
        self,
        exc_type: type[BaseException] | None,
        exc_value: BaseException | None,
        traceback: TracebackType | None,
        /,
    ) -> bool:
        assert self._cloned is not None
        if exc_type is None:
            # copy the contents from self._cloned to self._cursor
            await copy_extension(src=self._cloned, dst=self._cursor)
        await self._cloned.dispose()
        self._cloned = None
        return False


async def run_atom(
    rc: RocqCursor,
    goal: int,
    tac: str,
    *,
    pre: rdm_api.ProofState,
    trace: int | None = None,
) -> RunCommandResult:
    """Evalute the tactic in the current state"""

    dbg_trace(trace, f'run_command("{goal + 1}: {tac}.")')
    result = await rc.run_command(f"{goal + 1}: {tac}.")
    if isinstance(result, rdm_api.Err):
        return result
    return result.proof_state


async def run_on_all(
    rc: RocqCursor,
    tactic: str,
    run_tactic: LtacThunk,
    *,
    goals: tuple[int, int],
    multi_goal: bool = False,
    trace: int | None = None,
) -> int:
    """Returns the number of goals resulting from applying
    `tactic` to the goals. This is just the number of goals from that range,
    if `goals` does not include some goals, then these will not be included in the
    count.
    """
    dbg_trace(trace, f"run_atom({tactic}, {goals})")
    _, count = goals
    if multi_goal:
        raise NotImplementedError()
    else:
        return await run_on_goals(
            rc, [run_tactic] * count, goals=goals, trace=trace_indent(trace)
        )


async def run_on_goals(
    rc: RocqCursor,
    tacs: Sequence[LtacThunk | None],
    *,
    goals: tuple[int, int] = (0, 1),
    trace: int | None = None,
) -> int:
    """Run the given sequence of tactics on the goals.

    Arguments
      - rc -- the RocqCursor
      - tacs -- the tactics to run. There should be one for each goal.
          Use `None` to represent "do nothing".
      - goals -- the goals to run the tactics on, as (start, count)
      - trace -- whether to print logging information
    Return
      The number of goals produced (excludes goals outside of the input range)."""
    dbg_trace(trace, f"run_on_goals({tacs}, {goals})")
    first_goal, count = goals
    if len(tacs) != count:
        raise LtacFail()

    # If this is a single-goal tactic, then we run the tactic on each
    # goal.
    base = first_goal
    current_goal = await rc.current_goal()
    if current_goal is None:
        raise NotImplementedError()
    for i, run_tactic in enumerate(tacs):
        if run_tactic is None:
            base += 1
        else:
            pf_state = await run_tactic(rc, base, trace=trace, pre=current_goal)
            if isinstance(pf_state, rdm_api.Err):
                raise LtacFail(pf_state)
            else:
                # diff current_goal[base+1] with result[base:]
                if pf_state is None:
                    assert i == count - 1
                    return 0
                elif base + 1 < len(current_goal.focused_goals):
                    try:
                        base = pf_state.focused_goals[base:].index(
                            current_goal.focused_goals[base + 1]
                        )
                    except ValueError as err:
                        print("- " + "\n- ".join(pf_state.focused_goals))
                        raise NotImplementedError(
                            f"Failed to find next goal. Tactic is likely a multi-goal tactic. {run_tactic}"
                        ) from err
                    current_goal = pf_state
                else:
                    assert i == count - 1
                    return len(pf_state.focused_goals) - first_goal
    return base - first_goal


def decomp_run_curry(
    tactic: TacticAST,
    *,
    run_atom: TacticRunner = run_atom,
) -> LtacThunk:
    class Runner:
        """A special class so that we can override the `__str__` method"""

        async def __call__(
            self,
            rc: RocqCursor,
            goal: int,
            *,
            pre: rdm_api.ProofState,
            trace: int | None = None,
        ) -> RunCommandResult:
            nonlocal tactic, run_atom
            _count = await interp_tactic(
                rc, tactic, goals=(goal, 1), trace=trace, run_atom=run_atom
            )
            return await rc.current_goal()

        def __str__(self) -> str:
            nonlocal tactic
            return f"TacticRunner{tactic}"

    return Runner()


def dbg_trace(trace: int | None, msg: str) -> None:
    if trace is None:
        return
    print(" " * trace + f"> {msg}", flush=True)


def trace_indent(trace: int | None) -> int | None:
    return None if trace is None else (trace + 2)


async def interp_tactic(
    rc: RocqCursor,
    tactic: TacticAST,
    *,
    goals: tuple[int, int] = (0, 1),
    run_atom: TacticRunner = run_atom,
    trace: int | None = None,
) -> int:
    """Interprets the tactic AST at the current RocqCursor.

    Arguments
      - rc -- the cursor to run the tactics in
      - tactic -- the tactic AST to evaluate
      - goals -- the range of goals to run the tactic on (start, count)
      - run_atom -- function to evaluate an atomic tactic
      - trace -- whether to print debugging information
    Return
      - the number of resulting goals from evaluating the tactic.
        This does *not* count the goals that are not included in `goals`.
    Throws
      - LtacFail -- if the tactic fails
    """
    dbg_trace(trace, f"interp_rec({json.dumps(tactic)}, {goals})")
    first_goal, count = goals
    match tactic[0]:
        case "Atom":
            assert isinstance(tactic[1], str)
            tac: str = tactic[1]

            class MyTac:
                async def __call__(
                    self,
                    rc: RocqCursor,
                    goal: int,
                    *,
                    pre: rdm_api.ProofState,
                    trace: int | None = None,
                ) -> RunCommandResult:
                    nonlocal tac
                    return await run_atom(rc, goal, tac, trace=trace, pre=pre)

                def __str__(self) -> str:
                    nonlocal tac
                    return tac

            return await run_on_all(
                rc, cast(str, tac), MyTac(), goals=goals, trace=trace_indent(trace)
            )
        case "Then":
            [_, tac1, tac2] = tactic
            # assert isinstance(tac1, TacticAST)
            # assert isinstance(tac2, TacticAST)
            async with LtacTry(rc) as rc_attempt:
                new_goals = await interp_tactic(
                    rc_attempt,
                    cast(TacticAST, tac1),
                    goals=goals,
                    run_atom=run_atom,
                    trace=trace_indent(trace),
                )
                return await interp_tactic(
                    rc_attempt,
                    cast(TacticAST, tac2),
                    goals=(first_goal, new_goals),
                    run_atom=run_atom,
                    trace=trace_indent(trace),
                )
        case "Thens":
            async with LtacTry(rc) as rc_attempt:
                new_goals = await interp_tactic(
                    rc_attempt,
                    cast(TacticAST, tactic[1]),
                    goals=goals,
                    run_atom=run_atom,
                    trace=trace_indent(trace),
                )
                if new_goals != len(tactic[2]):
                    raise LtacFail()
                return await run_on_goals(
                    rc_attempt,
                    [
                        decomp_run_curry(cast(TacticAST, tac), run_atom=run_atom)
                        for tac in tactic[2]
                    ],
                    goals=(first_goal, new_goals),
                    trace=trace_indent(trace),
                )
        case "Thens3":
            [_, tac, before, middle, after] = tactic
            async with LtacTry(rc) as rc_attempt:
                count = await interp_tactic(
                    rc_attempt,
                    cast(TacticAST, tac),
                    goals=goals,
                    run_atom=run_atom,
                    trace=trace_indent(trace),
                )
                return await interp_tactic(
                    rc_attempt,
                    ["ExtendTac", before, middle, after],
                    goals=(first_goal, count),
                    run_atom=run_atom,
                    trace=trace_indent(trace),
                )
        case "ExtendTac":
            [_, before, middle, after] = tactic
            if count < len(before) + len(after):
                raise LtacFail()

            tacs: Sequence[LtacThunk | None] = (
                [
                    decomp_run_curry(cast(TacticAST, tac), run_atom=run_atom)
                    for tac in before
                ]
                + (
                    [decomp_run_curry(cast(TacticAST, middle), run_atom=run_atom)]
                    * (count - len(before) - len(after))
                )
                + [
                    decomp_run_curry(cast(TacticAST, tac), run_atom=run_atom)
                    for tac in after
                ]
            )
            return await run_on_goals(
                rc, tacs, goals=(first_goal, count), trace=trace_indent(trace)
            )
        case "Idtac":
            return count
        case "Fail":
            if tactic[1] not in ["fail", "fail 0"]:
                raise NotImplementedError(tactic[1])
            raise LtacFail()
        case "Time":
            tac = cast(TacticAST, tactic[1])
            return await interp_rec(
                rc, tac, goals=goals, run_atom=run_atom, trace=trace
            )
        case "Repeat":
            tac = cast(TacticAST, tactic[1])
            current = await rc.current_goal()
            while True:
                try:
                    async with LtacTry(rc) as rc_attempt:
                        count = await interp_rec(
                            rc_attempt,
                            tac,
                            goals=(first_goal, count),
                            run_atom=run_atom,
                            trace=trace_indent(trace),
                        )
                        if count == 0:
                            # solved the goal, so we stop
                            return count
                        new = await rc_attempt.current_goal()
                        if new == current:
                            # no (apparent) progress, so we stop
                            # If the goal changed, we must have made progress;
                            # however, it might be possible that the string
                            # representation of the goal did not change and we
                            # still made progress.
                            return count
                        current = new

                except LtacFail:
                    return count
            else:
                raise NotImplementedError(
                    "`repeat` ran for more than 50 steps without stopping. Potentially failed to detect termination."
                )

        case "Do":
            [_, n, tac] = tactic
            if n is None:
                raise NotImplementedError("`do` with unknown count")
            else:
                assert isinstance(n, int)
                for _ in range(0, n):
                    if count == 0:
                        return count
                    count = await interp_rec(
                        rc,
                        cast(TacticAST, tac),
                        goals=(first_goal, count),
                        run_atom=run_atom,
                        trace=trace_indent(trace),
                    )
                return count

        case "First":

            async def run_first(
                rc: RocqCursor,
                goal: int,
                *,
                pre: rdm_api.ProofState,
                trace: int | None = None,
            ) -> RunCommandResult:
                nonlocal tactic
                for t in cast(list[TacticAST], tactic[1:]):
                    try:
                        async with LtacTry(rc) as rc_attempt:
                            _ = await interp_tactic(
                                rc_attempt,
                                t,
                                goals=(goal, 1),
                                run_atom=run_atom,
                                trace=trace,
                            )
                            return await rc_attempt.current_goal()
                    except LtacFail:
                        continue
                raise LtacFail()

            return await run_on_all(
                rc, "<first>", run_first, goals=goals, trace=trace_indent(trace)
            )

        case "Solve":

            async def run_solve(
                rc: RocqCursor,
                goal: int,
                *,
                pre: rdm_api.ProofState,
                trace: int | None = None,
            ) -> RunCommandResult:
                nonlocal tactic
                for t in cast(list[TacticAST], tactic[1:]):
                    try:
                        async with LtacTry(rc) as rc_attempt:
                            count = await interp_tactic(
                                rc_attempt,
                                t,
                                goals=(goal, 1),
                                trace=trace,
                                run_atom=run_atom,
                            )
                            if count > 0:
                                raise LtacFail()
                        return await rc.current_goal()
                    except LtacFail:
                        continue
                raise LtacFail()

            return await run_on_all(rc, "<solve>", run_solve, goals=goals)

        case "Try":

            async def run_try(
                rc: RocqCursor,
                goal: int,
                *,
                pre: rdm_api.ProofState,
                trace: int | None = None,
            ) -> RunCommandResult:
                nonlocal tactic
                t = cast(TacticAST, tactic[1])
                try:
                    async with LtacTry(rc) as rc_attempt:
                        await interp_tactic(
                            rc_attempt,
                            t,
                            goals=(goal, 1),
                            trace=trace,
                            run_atom=run_atom,
                        )
                except LtacFail:
                    pass
                return await rc.current_goal()

            return await run_on_all(rc, "<try>", run_try, goals=goals, trace=trace)

    raise NotImplementedError(tactic)


async def interp_tactic_str(
    rc: RocqCursor,
    tactic: str,
    *,
    goals: tuple[int, int] = (0, 1),
    run_atom: TacticRunner = run_atom,
    trace: int | None = None,
) -> int:
    """Interpret a tactic from a string.
    This is equivalent to calling `parse_tac` and passing the result
    to `interp`."""
    explanation = await parse_tactic(rc, tactic)
    if isinstance(explanation, rdm_api.Err):
        raise ValueError(f"Failed to parse tactic: {tactic}")
    return await interp_tactic(
        rc, explanation, goals=goals, run_atom=run_atom, trace=trace
    )


async def parse_tactic(rc: RocqCursor, text: str) -> TacticAST | rdm_api.Err[None]:
    """Parse a tactic and return its AST."""
    if not text.endswith("."):
        text = f"{text}."
    explanation = await rc.query(f"info.Ltac {text}")
    if isinstance(explanation, rdm_api.Err):
        return explanation
    return json.loads(explanation.feedback_messages[0].text)

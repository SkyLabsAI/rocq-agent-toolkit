import json
from collections.abc import Sequence
from contextlib import AbstractAsyncContextManager
from types import TracebackType
from typing import Protocol, cast

from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_dune_util import DuneRocqPlugin

type RunCommandResult = rdm_api.ProofState | None | rdm_api.Err


class AtomCallback(Protocol):
    """Protocol for evaluating atomic tactics"""

    async def __call__(
        self, rc: RocqCursor, goal: int, tac: str, *, trace: int | None = None
    ) -> RunCommandResult: ...


class LtacThunk(Protocol):
    async def __call__(
        self, rc: RocqCursor, goal: int, *, trace: int | None = None
    ) -> RunCommandResult: ...


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


async def run_tac(
    rc: RocqCursor, goal: int, tac: str, *, trace: int | None = None
) -> RunCommandResult:
    """Evalute the tactic in the current state"""

    dbg_trace(trace, f'run_command("{goal + 1}: {tac}.")')
    result = await rc.run_command(f"{goal + 1}: {tac}.")
    if isinstance(result, rdm_api.Err):
        return result
    return result.proof_state


async def run_on_each(
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
    else:
        focused_goals = current_goal.focused_goals
    for i, run_tactic in enumerate(tacs):
        if run_tactic is None:
            base += 1
        else:
            result = await run_tactic(rc, base, trace=trace)
            if isinstance(result, rdm_api.Err):
                raise LtacFail(result)
            else:
                # diff current_goal[base+1] with result[base:]
                pf_state = result
                if pf_state is None:
                    assert i == count - 1
                    return 0
                elif base + 1 < len(focused_goals):
                    try:
                        base = pf_state.focused_goals[base:].index(
                            focused_goals[base + 1]
                        )
                    except ValueError:
                        print("- " + "\n- ".join(pf_state.focused_goals))
                        raise
                    focused_goals = pf_state.focused_goals
                else:
                    assert i == count - 1
                    return len(pf_state.focused_goals) - first_goal
    return base - first_goal


def decomp_run_curry(
    tactic: TacticAST,
    *,
    run_atom: AtomCallback = run_tac,
) -> LtacThunk:
    async def run(
        rc: RocqCursor, goal: int, *, trace: int | None = None
    ) -> RunCommandResult:
        _count = await interp_rec(
            rc, tactic, goals=(goal, 1), trace=trace, run_atom=run_atom
        )
        return await rc.current_goal()

    return run


def dbg_trace(trace: int | None, msg: str) -> None:
    if trace is None:
        return
    print(" " * trace + f"> {msg}", flush=True)


def trace_indent(trace: int | None) -> int | None:
    return None if trace is None else (trace + 2)


async def interp_rec(
    rc: RocqCursor,
    tactic: TacticAST,
    *,
    goals: tuple[int, int] = (0, 1),
    run_atom: AtomCallback = run_tac,
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
            tac = tactic[1]
            assert isinstance(tac, str)

            async def lam_run_tac(
                rc: RocqCursor, goal: int, *, trace: int | None = None
            ) -> RunCommandResult:
                return await run_atom(rc, goal, cast(str, tac), trace=trace)

            return await run_on_each(
                rc, cast(str, tac), lam_run_tac, goals=goals, trace=trace_indent(trace)
            )
        case "Then":
            [_, tac1, tac2] = tactic
            # assert isinstance(tac1, TacticAST)
            # assert isinstance(tac2, TacticAST)
            async with LtacTry(rc) as rc_attempt:
                new_goals = await interp_rec(
                    rc_attempt,
                    cast(TacticAST, tac1),
                    goals=goals,
                    run_atom=run_atom,
                    trace=trace_indent(trace),
                )
                return await interp_rec(
                    rc_attempt,
                    cast(TacticAST, tac2),
                    goals=(first_goal, new_goals),
                    run_atom=run_atom,
                    trace=trace_indent(trace),
                )
        case "Thens":
            async with LtacTry(rc) as rc_attempt:
                new_goals = await interp_rec(
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
                count = await interp_rec(
                    rc_attempt,
                    cast(TacticAST, tac),
                    goals=goals,
                    run_atom=run_atom,
                    trace=trace_indent(trace),
                )
                return await interp_rec(
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
                rc: RocqCursor, goal: int, *, trace: int | None = None
            ) -> RunCommandResult:
                nonlocal tactic
                for t in cast(list[TacticAST], tactic[1:]):
                    try:
                        async with LtacTry(rc) as rc_attempt:
                            _ = await interp_rec(
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

            return await run_on_each(
                rc, "<first>", run_first, goals=goals, trace=trace_indent(trace)
            )

        case "Solve":

            async def run_solve(
                rc: RocqCursor, goal: int, *, trace: int | None = None
            ) -> RunCommandResult:
                nonlocal tactic
                for t in cast(list[TacticAST], tactic[1:]):
                    try:
                        async with LtacTry(rc) as rc_attempt:
                            count = await interp_rec(
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

            return await run_on_each(rc, "<solve>", run_solve, goals=goals)

        case "Try":

            async def run_try(
                rc: RocqCursor, goal: int, *, trace: int | None = None
            ) -> RunCommandResult:
                nonlocal tactic
                t = cast(TacticAST, tactic[1])
                try:
                    async with LtacTry(rc) as rc_attempt:
                        await interp_rec(
                            rc_attempt,
                            t,
                            goals=(goal, 1),
                            trace=trace,
                            run_atom=run_atom,
                        )
                except LtacFail:
                    pass
                return await rc.current_goal()

            return await run_on_each(rc, "<try>", run_try, goals=goals, trace=trace)

    raise NotImplementedError(tactic)


async def interp_tactic(
    rc: RocqCursor,
    tactic: str,
    *,
    goals: tuple[int, int] = (0, 1),
    run_atom: AtomCallback = run_tac,
    trace: int | None = None,
) -> int:
    """Interpret a tactic from a string.
    This is equivalent to calling `parse_tac` and passing the result
    to `interp`."""
    explanation = await parse_tactic(rc, tactic)
    return await interp_rec(
        rc, explanation, goals=goals, run_atom=run_atom, trace=trace
    )


async def parse_tactic(rc: RocqCursor, text: str) -> TacticAST:
    """Parse a tactic and return its AST."""
    if not text.endswith("."):
        text = f"{text}."
    explanation = await rc.query(f"info.Ltac {text}")
    if isinstance(explanation, rdm_api.Err):
        raise Exception("Failed to parse tactic.", explanation)
    return json.loads(explanation.feedback_messages[0].text)

import asyncio
import json
import sys
from collections.abc import Awaitable, Callable, Sequence
from contextlib import AbstractAsyncContextManager
from types import TracebackType
from typing import cast

from rocq_doc_manager import RocqCursor, rc_sess
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_doc_manager.locator import LocatorParser
from rocq_dune_util import rocq_args_for
from rocq_dune_util.rocq_dune_util import DuneRocqPlugin

type TacticAST = list[str | TacticAST]


class LtacFail(Exception):
    pass


type RunCommandResult = rdm_api.ProofState | None | rdm_api.Err


class LtacTry(AbstractAsyncContextManager):
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
            start_prefix = await self._cursor.doc_prefix()
            end_prefix = await self._cloned.doc_prefix()
            assert end_prefix[0 : len(start_prefix)] == start_prefix
            for i in end_prefix[len(start_prefix) :]:
                if i.kind == "blanks":
                    await self._cursor.insert_blanks(i.text)
                else:
                    await self._cursor.insert_command(
                        i.text, ghost=i.kind == "ghost", blanks=None
                    )
        await self._cloned.dispose()
        self._cloned = None
        return False


def run_tac(
    tac: str,
) -> Callable[[RocqCursor, int], Awaitable[RunCommandResult]]:
    """The goal is 0-based"""

    async def result(rc: RocqCursor, goal: int) -> RunCommandResult:
        print(f'  > run_command("{goal + 1}: {tac}.")')
        result = await rc.run_command(f"{goal + 1}: {tac}.")
        if isinstance(result, rdm_api.Err):
            return result
        return result.proof_state

    return result


async def run_on_each(
    rc: RocqCursor,
    tactic: str,
    run_tactic: Callable[[RocqCursor, int], Awaitable[RunCommandResult]],
    *,
    goals: tuple[int, int],
    multi_goal: bool = False,
) -> int:
    """Returns the number of goals resulting from applying
    `tactic` to the goals. This is just the number of goals from that range,
    if `goals` does not include some goals, then these will not be included in the
    count.
    """
    print(f" > run_atom({tactic}, {goals})")
    _, count = goals
    if multi_goal:
        raise NotImplementedError()
    else:
        return await run_on_goals(rc, [run_tactic] * count, goals=goals)


async def run_on_goals(
    rc: RocqCursor,
    tacs: Sequence[Callable[[RocqCursor, int], Awaitable[RunCommandResult]] | None],
    goals: tuple[int, int] = (0, 1),
) -> int:
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
            result = await run_tactic(rc, base)
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


def decomp_run_lam(
    tactic: TacticAST,
) -> Callable[[RocqCursor, int], Awaitable[RunCommandResult]]:
    async def run(rc: RocqCursor, goal: int) -> RunCommandResult:
        _count = await decomp_run(rc, tactic, goals=(goal, 1))
        return await rc.current_goal()

    return run


async def decomp_run(
    rc: RocqCursor, tactic: TacticAST, *, goals: tuple[int, int]
) -> int:
    print(f" > decomp_run({json.dumps(tactic)}, {goals})")
    first_goal, count = goals
    match tactic[0]:
        case "Atom":
            tac = tactic[1]
            assert isinstance(tac, str)
            return await run_on_each(rc, cast(str, tac), run_tac(tac), goals=goals)
        case "Then":
            [_, tac1, tac2] = tactic
            # assert isinstance(tac1, TacticAST)
            # assert isinstance(tac2, TacticAST)
            async with LtacTry(rc) as rc_attempt:
                new_goals = await decomp_run(
                    rc_attempt, cast(TacticAST, tac1), goals=goals
                )
                return await decomp_run(
                    rc_attempt, cast(TacticAST, tac2), goals=(first_goal, new_goals)
                )
        case "Thens":
            async with LtacTry(rc) as rc_attempt:
                new_goals = await decomp_run(
                    rc_attempt, cast(TacticAST, tactic[1]), goals=goals
                )
                if new_goals != len(tactic[2]):
                    raise LtacFail()
                return await run_on_goals(
                    rc_attempt,
                    [decomp_run_lam(cast(TacticAST, tac)) for tac in tactic[2]],
                    goals=(first_goal, new_goals),
                )
        case "Thens3":
            [_, tac, before, middle, after] = tactic
            async with LtacTry(rc) as rc_attempt:
                count = await decomp_run(rc_attempt, cast(TacticAST, tac), goals=goals)
                return await decomp_run(
                    rc_attempt,
                    ["ExtendTac", before, middle, after],
                    goals=(first_goal, count),
                )
        case "ExtendTac":
            [_, before, middle, after] = tactic
            if count < len(before) + len(after):
                raise LtacFail()

            tacs: Sequence[
                Callable[[RocqCursor, int], Awaitable[RunCommandResult]] | None
            ] = (
                [decomp_run_lam(cast(TacticAST, tac)) for tac in before]
                + (
                    [decomp_run_lam(cast(TacticAST, middle))]
                    * (count - len(before) - len(after))
                )
                + [decomp_run_lam(cast(TacticAST, tac)) for tac in after]
            )
            return await run_on_goals(rc, tacs, goals=(first_goal, count))
        case "Idtac":
            return count
        case "Fail":
            if tactic[1] not in ["fail", "fail 0"]:
                raise NotImplementedError(tactic[1])
            raise LtacFail()
        case "First":

            async def run_first(rc: RocqCursor, goal: int) -> RunCommandResult:
                nonlocal tactic
                for t in cast(list[TacticAST], tactic[1:]):
                    try:
                        async with LtacTry(rc) as rc_attempt:
                            _ = await decomp_run(rc_attempt, t, goals=(goal, 1))
                            return await rc_attempt.current_goal()
                    except LtacFail:
                        continue
                raise LtacFail()

            return await run_on_each(rc, "<first>", run_first, goals=goals)

        case "Solve":

            async def run_solve(rc: RocqCursor, goal: int) -> RunCommandResult:
                nonlocal tactic
                for t in cast(list[TacticAST], tactic[1:]):
                    try:
                        async with LtacTry(rc) as rc_attempt:
                            count = await decomp_run(rc_attempt, t, goals=(goal, 1))
                            if count > 0:
                                raise LtacFail()
                        return await rc.current_goal()
                    except LtacFail:
                        continue
                raise LtacFail()

            return await run_on_each(rc, "<solve>", run_solve, goals=goals)

        case "Try":

            async def run_try(rc: RocqCursor, goal: int) -> RunCommandResult:
                nonlocal tactic
                t = cast(TacticAST, tactic[1])
                try:
                    async with LtacTry(rc) as rc_attempt:
                        await decomp_run(rc_attempt, t, goals=(goal, 1))
                except LtacFail:
                    pass
                return await rc.current_goal()

            return await run_on_each(rc, "<try>", run_try, goals=goals)

        case ctor:
            raise NotImplementedError(ctor)

    return []


async def amain(file: str, locator: str) -> int:
    plugin = DuneRocqPlugin(
        opam_pkg="rocq-tactic-parser", entry_points=["theories/explain.v"]
    )
    rocq_args = rocq_args_for(file, plugins=[plugin])
    async with rc_sess(file, rocq_args=rocq_args) as rc:
        assert isinstance(
            await rc.run_command("Require Import skylabs_ai.tactic_parser.explain."),
            rdm_api.CommandData,
        )
        assert await LocatorParser.parse(locator).go_to(rc)

        suffix = await rc.doc_suffix()
        for i, tactic in enumerate([t for t in suffix if t.kind == "command"]):
            if tactic.data and tactic.data.kind in ["EndProof"]:
                break
            tac_str = tactic.text
            print(f"{i}/ {tac_str}")
            explanation = await rc.query(f"Explain {tac_str}")
            if isinstance(explanation, rdm_api.Err):
                print("query failed!")
                raise Exception("Oops")
            explanation = json.loads(explanation.feedback_messages[0].text)
            count = await decomp_run(rc, explanation, goals=(0, 1))
            print(f"> ({count})")
            print("")
    return 0


def main() -> int:
    return asyncio.run(amain(sys.argv[1], sys.argv[2]))


if __name__ == "__main__":
    sys.exit(main())

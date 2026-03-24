import asyncio
import json
import sys
from collections.abc import Awaitable, Callable
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
    first_goal, count = goals
    if multi_goal:
        raise NotImplementedError()
    else:
        # If this is a single-goal tactic, then we run the tactic on each
        # goal.
        base = first_goal
        current_goal = await rc.current_goal()
        if current_goal is None:
            raise NotImplementedError()
        else:
            focused_goals = current_goal.focused_goals
        for i in range(0, count):
            result = await run_tactic(rc, base)
            if isinstance(result, rdm_api.Err):
                raise LtacFail(result)
            else:
                # diff current_goal[base+1] with result[base:]
                pf_state = result
                if pf_state is None:
                    raise NotImplementedError()
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


async def decomp_run(
    rc: RocqCursor, tactic: TacticAST, *, goals: tuple[int, int]
) -> tuple[int, int]:
    print(f" > decomp_run({json.dumps(tactic)}, {goals})")
    first_goal, count = goals
    match tactic[0]:
        case "Atom":
            tac = tactic[1]
            assert isinstance(tac, str)
            result = await run_on_each(rc, cast(str, tac), run_tac(tac), goals=goals)
            return (first_goal, result)
        case "Then":
            [_, tac1, tac2] = tactic
            # assert isinstance(tac1, TacticAST)
            # assert isinstance(tac2, TacticAST)
            new_goals = await decomp_run(rc, cast(TacticAST, tac1), goals=goals)
            return await decomp_run(rc, cast(TacticAST, tac2), goals=new_goals)
        case "Idtac":
            return goals
        case "Fail":
            if tactic[1] not in ["fail", "fail 0"]:
                raise NotImplementedError(tactic[1])
            raise LtacFail()
        case "First":

            async def run_first(rc: RocqCursor, goal: int) -> RunCommandResult:
                nonlocal tactic
                for t in cast(list[TacticAST], tactic[1:]):
                    try:
                        async with (await rc.clone()).sess() as rc_attempt:
                            _ = await decomp_run(rc_attempt, t, goals=(goal, 1))
                        # TODO: this is not an efficient implementation of try
                        print(">>>>>>>>>>>>>> REPLICATE")
                        await decomp_run(rc, t, goals=(goal, 1))
                        print("<<<<<<<<<<<<<< REPLICATE")
                        return await rc.current_goal()
                    except NotImplementedError:
                        raise
                    except LtacFail:
                        continue
                raise LtacFail()

            new_count = await run_on_each(rc, "<first>", run_first, goals=goals)
            return (first_goal, new_count)

        case "Solve":

            async def run_solve(rc: RocqCursor, goal: int) -> RunCommandResult:
                nonlocal tactic
                for t in cast(list[TacticAST], tactic[1:]):
                    try:
                        async with (await rc.clone()).sess() as rc_attempt:
                            _, count = await decomp_run(rc_attempt, t, goals=(goal, 1))
                            if count > 0:
                                raise LtacFail()

                        print(">>>>>>>>>>>>>> REPLICATE")
                        _, count = await decomp_run(rc, t, goals=(goal, 1))
                        print("<<<<<<<<<<<<<< REPLICATE")
                        assert count == 0
                        return await rc.current_goal()
                    except LtacFail:
                        continue
                raise LtacFail()

            new_count = await run_on_each(rc, "<solve>", run_solve, goals=goals)
            return (first_goal, new_count)

        case "Try":

            async def run_try(rc: RocqCursor, goal: int) -> RunCommandResult:
                nonlocal tactic
                t = cast(TacticAST, tactic[1])
                try:
                    async with (await rc.clone()).sess() as rc_attempt:
                        await decomp_run(rc_attempt, t, goals=(goal, 1))
                    print(">>>>>>>>>>>>>> REPLICATE")
                    await decomp_run(rc, t, goals=(goal, 1))
                    print("<<<<<<<<<<<<<< REPLICATE")
                except LtacFail:
                    pass
                return await rc.current_goal()

            new_count = await run_on_each(rc, "<try>", run_try, goals=goals)
            return (first_goal, new_count)

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
            (start, count) = await decomp_run(rc, explanation, goals=(0, 1))
            print(f"> ({start}, {count})")
            print("")
    return 0


def main() -> int:
    return asyncio.run(amain(sys.argv[1], sys.argv[2]))


if __name__ == "__main__":
    sys.exit(main())

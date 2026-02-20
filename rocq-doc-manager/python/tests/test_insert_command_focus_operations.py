from pathlib import Path

import pytest

# # from rocq_doc_manager_api import CommandData, Err, CommandError
# from rocq_doc_manager.rocq_doc_manager_api import (
#     CommandData,
#     CommandError,
#     Err,
#     RocqCursor,
#     rc_sess,
# )
# from rocq_doc_manager import RocqCursor
# from rocq_doc_manager.rocq_cursor_protocol import RocqCursor
from rocq_doc_manager import RocqCursor, rc_sess
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_doc_manager.locator import (
    LocatorParser,
)


async def check(rc: RocqCursor, loc: str, expected: int, next: bool = False) -> None:
    assert await LocatorParser.parse(loc).go_to(rc, next=next)
    assert await rc.cursor_index() == expected, f"{loc}"


@pytest.mark.asyncio
async def test_insert_focus_ops() -> None:
    p = Path(__file__).parent / "locator_test.v"
    async with rc_sess(str(p), load_file=True) as rc:
        await check(rc, "admit", 4)
        command_reply = await rc.insert_command("{")
        assert not isinstance(command_reply, rdm_api.Err)
        command_reply = await rc.insert_command("-")
        assert not isinstance(command_reply, rdm_api.Err)
        command_reply = await rc.insert_command("+")
        assert not isinstance(command_reply, rdm_api.Err)
        command_reply = await rc.insert_command("*")
        assert not isinstance(command_reply, rdm_api.Err)


@pytest.mark.asyncio
async def test_run_focus_ops() -> None:
    p = Path(__file__).parent / "locator_test.v"
    rc: RocqCursor
    async with rc_sess(str(p), load_file=True) as rc:
        await check(rc, "admit", 4)
        command_reply = await rc.run_command("{")
        assert not isinstance(command_reply, rdm_api.Err)
        command_reply = await rc.run_command("-")
        assert not isinstance(command_reply, rdm_api.Err)
        command_reply = await rc.run_command("+")
        assert not isinstance(command_reply, rdm_api.Err)
        command_reply = await rc.run_command("*")
        assert not isinstance(command_reply, rdm_api.Err)


@pytest.mark.asyncio
async def test_insert_bullet_followed_by_tactic() -> None:
    p = Path(__file__).parent / "locator_test.v"
    async with rc_sess(str(p), load_file=True) as rc:
        await check(rc, "admit", 4)

        initial_goal = await rc.current_goal()
        solving_tac = "exact I."
        solved_goal = rdm_api.ProofState(
            focused_goals=[],
            unfocused_goals=[],
            shelved_goals=0,
            given_up_goals=0,
        )
        assert initial_goal != solved_goal

        # Check that `solving_tac` actually closes the goal
        async with rc.ctx(rollback=True):
            command_reply = await rc.insert_command(solving_tac)
            assert not isinstance(command_reply, rdm_api.Err)
            new_goal = command_reply.proof_state

            assert initial_goal != new_goal
            assert new_goal == solved_goal

        # Check behavior of `insert_command` when tactics are prefixed by bullets
        #
        # Note: effect of solving_tac is ignored if an initial bullet is included.
        for bullet in ["-", "+", "*"]:
            bulleted_solving_tac = f"{bullet} {solving_tac}"

            command_reply = await rc.insert_command(bulleted_solving_tac)
            assert not isinstance(command_reply, rdm_api.Err)
            new_goal = command_reply.proof_state

            doc_prefix_text = [item.text for item in await rc.doc_prefix()]
            assert solving_tac not in doc_prefix_text
            assert bulleted_solving_tac in doc_prefix_text

            assert initial_goal != new_goal
            assert new_goal == solved_goal, " ".join(
                [
                    "RocqDocManager will happily insert '{bullet} {tactic}'."
                    "While the corresponding `PrefixItem.text` includes {tactic}, its effect seems to be ignored.",
                    "RocqDocManager should either process all of '{bullet} {tactic}' -- potentially producing two",
                    "PrefixItems -- or it should return an error indicating that bullets must be separated from tactics.",
                ]
            )

from pathlib import Path

import pytest
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

        initial_goal = await rc.current_goal()

        for begin_focus in ["-", "+", "*"]:
            async with rc.ctx(rollback=True):
                command_reply = await rc.insert_command(begin_focus)
                assert not isinstance(command_reply, rdm_api.Err)
                assert command_reply.proof_state is not None
                new_goal = command_reply.proof_state

                assert initial_goal != new_goal
                # `new_goal` only differs from `initial_goal` in that `unfocused_goals`
                # is tracking that no goals remain when the focus is "popped"
                assert initial_goal == rdm_api.ProofState(
                    focused_goals=new_goal.focused_goals,
                    unfocused_goals=[],
                    shelved_goals=new_goal.shelved_goals,
                    given_up_goals=new_goal.given_up_goals,
                )


@pytest.mark.asyncio
async def test_run_focus_ops() -> None:
    p = Path(__file__).parent / "locator_test.v"
    rc: RocqCursor
    async with rc_sess(str(p), load_file=True) as rc:
        await check(rc, "admit", 4)

        initial_goal = await rc.current_goal()

        for begin_focus in ["{", "-", "+", "*"]:
            command_reply = await rc.run_command(begin_focus)
            assert not isinstance(command_reply, rdm_api.Err)
            assert command_reply.proof_state is not None
            new_goal = command_reply.proof_state

            assert initial_goal != new_goal
            # `new_goal` only differs from `initial_goal` in that `unfocused_goals`
            # is tracking that no goals remain when the focus is "popped"
            assert initial_goal == rdm_api.ProofState(
                focused_goals=new_goal.focused_goals,
                unfocused_goals=[],
                shelved_goals=new_goal.shelved_goals,
                given_up_goals=new_goal.given_up_goals,
            )

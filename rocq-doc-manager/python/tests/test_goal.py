from pathlib import Path

import pytest
from rocq_doc_manager import rc_sess
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_doc_manager.cursor import GoalRocqCursor


@pytest.mark.asyncio
async def test_full_proof() -> None:
    p = Path(__file__).parent / "test_goal.v"
    async with rc_sess(str(p), load_file=True) as rc:
        gc = await GoalRocqCursor.make(rc, start=6, count=0)
        assert isinstance(gc, GoalRocqCursor)
        # Checking that the prefix / index / suffix make sense.
        assert await gc.cursor_index() == 0
        assert len(await gc.doc_prefix()) == 0
        assert len(await gc.doc_suffix()) == 0
        # Trying to escape the goal.
        try:
            _ = await gc.run_command("Admitted.")
            raise AssertionError()
        except Exception as e:
            assert "escape" in str(e)
        # Making progress on the goal.
        data = await gc.run_command("split.")
        assert isinstance(data, rdm_api.CommandData)
        data = await gc.run_command("-")
        assert isinstance(data, rdm_api.CommandData)
        # Check that the goal is not closed.
        assert not await gc.closed()
        # Closing the goal.
        data = await gc.run_command("constructor.")
        assert isinstance(data, rdm_api.CommandData)
        data = await gc.run_command("-")
        assert isinstance(data, rdm_api.CommandData)
        data = await gc.run_command("reflexivity.")
        assert isinstance(data, rdm_api.CommandData)
        # Check that the goal is closed.
        assert await gc.closed()


@pytest.mark.asyncio
async def test_admit() -> None:
    p = Path(__file__).parent / "test_goal.v"
    async with rc_sess(str(p), load_file=True) as rc:
        gc = await GoalRocqCursor.make(rc, start=16, count=1)
        assert isinstance(gc, GoalRocqCursor)
        # Checking that the prefix / index / suffix make sense.
        assert await gc.cursor_index() == 0
        assert len(await gc.doc_prefix()) == 0
        assert len(await gc.doc_suffix()) == 1
        # Solving the goal.
        data = await gc.run_command("constructor.")
        assert isinstance(data, rdm_api.CommandData)
        # Trying to escape the goal.
        try:
            _ = await gc.run_command("-")
            raise AssertionError()
        except Exception as e:
            assert "escape" in str(e)
        # Check that the goal is closed.
        assert await gc.closed()

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
        await check(rc, "Proof.", 3)
        # command_reply: rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]
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
        await check(rc, "Proof.", 3)
        # command_reply: rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]
        command_reply = await rc.run_command("{")
        assert not isinstance(command_reply, rdm_api.Err)
        command_reply = await rc.run_command("-")
        assert not isinstance(command_reply, rdm_api.Err)
        command_reply = await rc.run_command("+")
        assert not isinstance(command_reply, rdm_api.Err)
        command_reply = await rc.run_command("*")
        assert not isinstance(command_reply, rdm_api.Err)

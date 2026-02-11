from collections.abc import AsyncIterator
from typing import Any

import pytest
import pytest_asyncio
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_doc_manager.rocq_cursor_protocol import RocqCursorProtocolAsync
from rocq_doc_manager.rocq_cursor_websocket import (
    CursorId,
    WSCursor,
    WSCursorServer,
    WSMux,
)
from websockets import connect, serve

from .util import RDM_Tests


@pytest.mark.asyncio
class Test_API(RDM_Tests):
    @pytest_asyncio.fixture
    @staticmethod
    async def async_rc() -> AsyncIterator[RocqCursorProtocolAsync]:
        """A websocket RocqCursor for a real file that can be loaded."""
        rc = RDM_Tests.mk_rdm(path="./tests/test.v").cursor()
        id = CursorId(cursor=0)

        async def handle(conn):
            server = WSCursorServer(conn, {id: rc})
            await server.serve()

        async with serve(handle, host="127.0.0.1", port=None) as server:
            (host, port) = list(server.sockets)[0].getsockname()
            async with connect(f"ws://{host}:{port}") as client:
                mux = WSMux(client)
                await mux.start()
                yield WSCursor.create(mux, id)

    async def test_1(self, async_rc: RocqCursorProtocolAsync) -> None:
        c = async_rc
        check_reply: Any
        check_reply = await c.query_text("Check nat.", index=0)
        assert check_reply == "nat\n     : Set"

        check_reply = await c.query_text("Check flurb.", index=0)
        assert isinstance(check_reply, rdm_api.Err)

    async def test_2(self, async_rc: RocqCursorProtocolAsync) -> None:
        c = async_rc
        c2 = await c.clone()

        check_reply: Any

        check_reply = await c2.query_text("Check nat.", index=0)
        assert check_reply == "nat\n     : Set"

        check_reply = await c2.query_text("Check flurb.", index=0)
        assert isinstance(check_reply, rdm_api.Err)

        check_reply = await c.insert_command("Definition flurb : True := I.")
        assert isinstance(check_reply, rdm_api.CommandData)
        check_reply = await c.insert_command("Definition flirb : True := flurb.")
        assert isinstance(check_reply, rdm_api.CommandData)

        with pytest.raises(Exception):  # noqa: B017
            check_reply = await c.query_text("Check flurb.", index=-1)
            print(check_reply)

        check_reply = await c2.query_text("Check flurb.", index=0)
        assert isinstance(check_reply, rdm_api.Err)

    async def test_3(self, async_rc: RocqCursorProtocolAsync) -> None:
        c = async_rc
        await c.insert_command("Goal True.")
        check_reply: Any
        check_reply = await c.run_command("exact tt.")
        assert isinstance(check_reply, rdm_api.Err)
        check_reply = await c.run_command("solve [auto].")
        assert isinstance(check_reply, rdm_api.CommandData)
        check_reply = await c.run_command("Qed.")
        assert isinstance(check_reply, rdm_api.CommandData)
        check_reply = await c.materialize()  # type: ignore[func-returns-value]
        assert check_reply is None

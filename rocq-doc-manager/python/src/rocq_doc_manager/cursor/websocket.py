from __future__ import annotations

import json
from typing import (
    Any,
    override,
)

from pydantic import BaseModel, ConfigDict

from rocq_doc_manager.microrpc.dispatcher import Dispatcher
from rocq_doc_manager.microrpc.tunnel import WSMux, proxy_protocol

from .. import rocq_doc_manager_api as rdm_api
from ..microrpc.deserialize import decoder, unguided_decoder
from .protocol import (
    RocqCursor,
    RocqCursorProtocolAsync,
)


class CursorId(BaseModel):
    """Fresh ids used in the websocket RPC. Not to be confused with the integer
    that represents cursors in the JsonRPC API"""

    model_config = ConfigDict(
        extra="forbid",
        frozen=True,
    )

    cursor: int


class ClosedOK(rdm_api.Error):
    def __init__(self):
        return super().__init__("Connection to remote cursor closed normally.")


class ClosedError(rdm_api.Error):
    def __init__(self):
        return super().__init__("Connection to remote cursor closed unexpectedly.")


# ===============================================================
#  Server Code
# ===============================================================


@proxy_protocol(
    RocqCursorProtocolAsync,
    passthru=["ctx", "aborted_goal_ctx", "Section", "goto_first_match"],
)
class WSCursor:
    """A cursor that proxies method calls through WSMux.

    NOTE: We cannot convince mypy that WSCursor implements
    RocqCursorProtocolAsync because we are not listing the methods explicitly."""

    _mux: WSMux  # shared between cloned cursors
    _id: CursorId  # unique to a single cursor

    def __init__(self, mux: WSMux, id: CursorId):
        self._mux = mux
        self._id = id

    @classmethod
    def create(cls, mux: WSMux, id: CursorId) -> RocqCursorProtocolAsync:
        return cls(mux, id)  # type: ignore[return-value]

    async def clone(self, **kwargs) -> WSCursor:
        cursor = await self._rpc(CursorId, "clone", [], kwargs)
        return WSCursor(self._mux, cursor)

    async def _rpc(
        self, ty: type, method: str, args: list[Any], kwargs: dict[str, Any]
    ):
        bundled_args: list[Any] = [self._id]
        bundled_args.extend(args)
        (is_exception, value_json) = await self._mux.send(method, bundled_args, kwargs)
        if not is_exception:
            value = decoder.decode(json.loads(value_json), ty)
        else:
            value = json.loads(value_json, object_hook=unguided_decoder.object_hook)
            assert isinstance(value, BaseException)
            raise value
        return value


class CursorDispatcher(Dispatcher):
    """This is a multi-dispatcher over `RocqCursorProtocol`.

    The first positional argument in each request is the cursor
    identifier. All of the other arguments are passed through to
    the corresponding cursor.
    """

    _cursors: dict[CursorId, RocqCursor]
    _fresh: int

    def __init__(self, cursors: dict[int, RocqCursor]):
        self._cursors = {
            CursorId(cursor=idx): cursor for idx, cursor in cursors.items()
        }
        self._fresh = max(cursors.keys())

    def extract_cursor(self, args: list[Any]) -> tuple[RocqCursor, list[Any]]:
        cursor_idx = args.pop(0)
        cursor = decoder.decode(cursor_idx, CursorId)
        # if not isinstance(cursor_idx, int):
        #     raise ValueError(f"Invalid cursor, expected integer, got '{cursor_idx}'")
        # cursor = CursorId(cursor=cursor_idx)
        if cursor not in self._cursors:
            raise ValueError(f"Unbound cursor. {cursor}")
        return (self._cursors[cursor], args)

    @override
    async def dispatch(
        self, method: str, args: list[Any], kwargs: dict[str, Any]
    ) -> Any:
        (cursor, args) = self.extract_cursor(args)
        match method:
            case "clone":

                async def fn(args, kwargs):
                    new_cursor = await cursor.clone()
                    self._fresh += 1
                    new_id = CursorId(cursor=self._fresh)
                    self._cursors[new_id] = new_cursor
                    return new_id
            case _:

                async def fn(args, kwargs):
                    # TODO: insert await below when wrapped cursors are async
                    return await getattr(cursor, method)(*args, **kwargs)

        return await fn(args, kwargs)

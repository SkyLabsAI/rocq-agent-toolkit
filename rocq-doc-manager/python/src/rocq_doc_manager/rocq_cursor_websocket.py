from __future__ import annotations

import dataclasses
import json
import traceback
from dataclasses import dataclass
from typing import (
    Any,
    override,
)

from pydantic import BaseModel

from rocq_doc_manager.microrpc.dipatcher import Dispatcher
from rocq_doc_manager.microrpc.tunnel import WSMux, proxy_protocol
from rocq_doc_manager.rocq_cursor_protocol import (
    RocqCursor,
    RocqCursorProtocolAsync,
)

from . import rocq_doc_manager_api as rdm_api
from .microrpc.deserialize import (
    Decoder,
    EncoderProtocol,
    TypeMismatch,
    UnguidedDecoder,
)


@dataclass(kw_only=True, frozen=True)
class CursorId:
    """Fresh ids used in the websocket RPC. Not to be confused with the integer
    that represents cursors in the JsonRPC API"""

    cursor: int


class Encoder(json.JSONEncoder, EncoderProtocol):
    def default(self, o: Any):
        if isinstance(o, rdm_api.Error):
            return {
                "_ty": "rdm_api.Error",
                "args": list(map(super().encode, o.args)),
                "traceback": traceback.format_tb(o.__traceback__),
            }
        if isinstance(o, Exception):  # less specific than [rdm_api.Error]
            return {
                "_ty": "Exception",
                "args": list(map(super().encode, o.args)),
                "traceback": traceback.format_tb(o.__traceback__),
            }
        elif isinstance(o, rdm_api.Err):
            return {"_ty": "rdm_api.Err", "message": o.message, "data": o.data}
        elif isinstance(o, rdm_api.Resp):
            return {"_ty": "rdm_api.Resp", "result": o.result}
        elif isinstance(o, BaseModel):
            return o.model_dump()
        elif dataclasses.is_dataclass(type(o)):
            result = {k.name: getattr(o, k.name) for k in dataclasses.fields(o)}
            assert "_ty" not in result
            result["_ty"] = o.__class__.__name__
            return result
        else:
            return super().default(o)


encoder = Encoder()


decoder = Decoder()


def decode_err(decode, payload, ty, params, env) -> rdm_api.Err:
    assert len(params) == 1
    data_ty = params[0]
    match payload:
        case {"_ty": "rdm_api.Err", "message": message, "data": data}:
            if not isinstance(message, str):
                raise TypeMismatch()
            data = decode(data, data_ty, [], env)
            return rdm_api.Err(message=message, data=data)
        case _:
            raise TypeMismatch()


def decode_resp(decode, payload, ty, params, env) -> rdm_api.Resp:
    assert len(params) == 1
    result_ty = params[0]
    match payload:
        case {"_ty": "rdm_api.Resp", "result": result}:
            result = decode(result, result_ty, [], env)
            return rdm_api.Resp(result=result)
        case _:
            raise TypeMismatch()


def decode_error(decode, payload, ty, params, env) -> rdm_api.Error:
    assert params == []
    match payload:
        case {"_ty": "rdm_api.Error", "args": args, "traceback": traceback}:
            e = rdm_api.Error(*args)
            e.__traceback__ = traceback
            return e
        case _:
            raise TypeMismatch()


def decode_exception(decode, payload, ty, params, env) -> Exception:
    assert params == []
    match payload:
        case {"_ty": "Exception", "args": args, "traceback": traceback}:
            e = Exception(*args)
            e.__traceback__ = traceback
            return e
        case _:
            raise TypeMismatch()


decoder.add_decoders(
    {
        rdm_api.Err: decode_err,
        rdm_api.Resp: decode_resp,
        rdm_api.Error: decode_error,
        Exception: decode_exception,
    }
)


unguided_decoder = UnguidedDecoder()


def ug_decode_exception(payload: Any) -> Exception:
    match payload:
        case {"args": args}:
            return Exception(*args)
        case _:
            raise TypeMismatch()


unguided_decoder.add_decoder("Exception", ug_decode_exception)


class ClosedOK(rdm_api.Error):
    def __init__(self):
        return super().__init__("Connection to remote cursor closed normally.")


class ClosedError(rdm_api.Error):
    def __init__(self):
        return super().__init__("Connection to remote cursor closed unexpectedly.")


# ===============================================================
#  Server Code
# ===============================================================


@proxy_protocol(RocqCursorProtocolAsync)
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

    def __init__(self, cursors: dict[CursorId, RocqCursor]):
        self._cursors = cursors
        self._fresh = max([c.cursor for c in cursors])

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
                    new_cursor = cursor.clone()
                    self._fresh += 1
                    new_id = CursorId(cursor=self._fresh)
                    self._cursors[new_id] = new_cursor
                    return new_id
            case _:

                async def fn(args, kwargs):
                    # TODO: insert await below when wrapped cursors are async
                    return getattr(cursor, method)(*args, **kwargs)

        return await fn(args, kwargs)

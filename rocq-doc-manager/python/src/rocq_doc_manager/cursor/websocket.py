from __future__ import annotations

import dataclasses
import inspect
import json
import traceback
from collections.abc import Callable
from dataclasses import dataclass
from typing import (
    Any,
    get_type_hints,
    override,
)

from pydantic import BaseModel, JsonValue, RootModel, TypeAdapter

from rocq_doc_manager.microrpc.dispatcher import Dispatcher, proxy_protocol
from rocq_doc_manager.microrpc.duplex import RPCClient

from .. import rocq_doc_manager_api as rdm_api
from ..microrpc.deserialize import (
    Decoder,
    EncoderProtocol,
    TypeMismatch,
    UnguidedDecoder,
)
from .protocol import (
    RocqCursor,
    RocqCursorProtocolAsync,
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


# class ClosedOK(rdm_api.Error):
#     def __init__(self):
#         return super().__init__("Connection to remote cursor closed normally.")


# class ClosedError(rdm_api.Error):
#     def __init__(self):
#         return super().__init__("Connection to remote cursor closed unexpectedly.")


# ===============================================================
#  The client code
# ===============================================================


@proxy_protocol(
    RocqCursorProtocolAsync,
    passthru=["ctx", "aborted_goal_ctx", "Section", "goto_first_match"],
)
class WSCursor:
    """A cursor that proxies method calls through an RPCClient.

    NOTE: We cannot convince mypy that WSCursor implements
    RocqCursorProtocolAsync because we are not listing the methods explicitly."""

    _mux: RPCClient  # shared between cloned cursors
    _id: CursorId  # unique to a single cursor

    def __init__(self, mux: RPCClient, id: CursorId):
        self._mux = mux
        self._id = id

    @classmethod
    def create(cls, mux: RPCClient, id: int) -> RocqCursorProtocolAsync:
        return cls(mux, CursorId(cursor=id))  # type: ignore[return-value]

    async def clone(self, *, materialize: bool = False) -> WSCursor:
        success, result = await self._rpc("clone", {"materialize": materialize})
        if success and isinstance(result, int):
            return WSCursor(self._mux, CursorId(cursor=result))
        else:
            raise RPCException(result)

    async def _rpc(
        self, method: str, params: dict[str, JsonValue] | None
    ) -> tuple[bool, JsonValue]:
        rpc_args: JsonValue
        if params is None:
            rpc_args = {}
        else:
            rpc_args = params.copy()
        rpc_args["<object>"] = self._id.cursor
        return await self._mux.send(method, rpc_args)
        # if not is_exception:
        #     value = decoder.decode(json.loads(value_json), ty)
        # else:
        #     value = json.loads(value_json, object_hook=unguided_decoder.object_hook)
        #     assert isinstance(value, BaseException)
        #     raise value
        # return value


# ===============================================================
#  The server code
# ===============================================================


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

    def extract_cursor(self, params: JsonValue) -> tuple[RocqCursor, JsonValue]:
        if isinstance(params, dict):
            idx = params.pop("!cursor")
            if idx is None:
                raise KeyError(f"Missing '<object>' parameter: {params}")
            if isinstance(idx, int):
                cursor = self._cursors.get(CursorId(cursor=idx))
                if cursor:
                    return (cursor, params)
                else:
                    raise ValueError(f"Unknown <object>={idx}: {params}")
            else:
                raise ValueError(
                    f"Invalid '<object>' parameter, expected int: {params}"
                )
        raise ValueError(f"Invalid message type, expected dict: {params}")

    async def default_dispatch_rpc[R](
        func: Callable[..., R], payload: JsonValue
    ) -> JsonValue:
        """
        Takes a Pydantic JsonValue, validates it against the function signature,
        executes the function, and returns the result as a JsonValue.
        """
        # 1. Ensure the payload is a mapping (dictionary) to match function kwargs
        if not isinstance(payload, dict):
            raise ValueError(f"RPC payload must be a dictionary, got {type(payload)}")

        # 2. Get function signature and type hints
        sig = inspect.signature(func)
        type_hints = get_type_hints(func)

        # 3. Validate arguments
        # We iterate through the signature to match payload keys to function parameters
        resolved_kwargs = {}
        for param_name, param in sig.parameters.items():
            if param_name == "self":
                continue

            if param_name in payload:
                param_type = type_hints.get(param_name, Any)
                # Use TypeAdapter to coerce the JsonValue into the specific Python type
                adapter = TypeAdapter(param_type)
                resolved_kwargs[param_name] = adapter.validate_python(
                    payload[param_name]
                )
            elif param.default is inspect.Parameter.empty:
                raise TypeError(f"Missing required argument: {param_name}")

        # 4. Execute the function (handling both sync and async)
        if inspect.iscoroutinefunction(func):
            result = await func(**resolved_kwargs)
        else:
            result = func(**resolved_kwargs)

        # 5. Convert return value back to a JsonValue
        # .model_dump(mode='json') ensures the output is a serializable JsonValue (dict/list/etc)
        return RootModel(result).model_dump(mode="json")

    @override
    async def dispatch(self, method: str, params: JsonValue) -> Any:
        (cursor, params) = self.extract_cursor(params)
        match method:
            case "clone":
                materialize = (
                    params.get("materialize", False)
                    if isinstance(params, dict)
                    else False
                )
                new_cursor = await cursor.clone(materialize=materialize)
                self._fresh += 1
                new_id = CursorId(cursor=self._fresh)
                self._cursors[new_id] = new_cursor
                return new_id
            case _:
                return await getattr(cursor, method)(*args)

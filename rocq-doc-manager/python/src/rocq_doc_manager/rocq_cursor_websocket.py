from __future__ import annotations

import asyncio
import dataclasses
import json
import traceback
from collections.abc import Callable
from dataclasses import dataclass
from functools import wraps
from types import FunctionType
from typing import (
    Any,
    Literal,
    Protocol,
    get_protocol_members,
    get_type_hints,
    is_protocol,
    overload,
    override,
)

import websockets

from rocq_doc_manager.rocq_cursor_protocol import (
    RocqCursorProtocol,
    RocqCursorProtocolAsync,
)

from . import rocq_doc_manager_api as rdm_api
from .deserialize import Decoder, TypeMismatch, UnguidedDecoder


@dataclass(kw_only=True, frozen=True)
class CursorId:
    """Fresh ids used in the websocket RPC. Not to be confused with the integer
    that represents cursors in the JsonRPC API"""

    cursor: int


@dataclass
class Request:
    id: int  # This is the JSON-RPC request ID
    method: str
    args: list[Any]
    kwargs: dict[str, Any]


@dataclass
class Response:
    id: int
    is_exception: bool
    payload: Any


class Encoder(json.JSONEncoder):
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
        return super("Connection to remote cursor closed normally.")


class ClosedError(rdm_api.Error):
    def __init__(self):
        return super("Connection to remote cursor closed unexpectedly.")


class WSConnection(Protocol):
    @overload
    async def send(self, message: bytes) -> None: ...
    @overload
    async def send(self, message: str) -> None: ...
    async def recv(self, decode: Literal[False]) -> bytes: ...
    async def close(self) -> None: ...


class _RPC(Protocol):
    """Internal protocol to document requirements on wrapped classes"""

    async def _rpc(
        self, ty: Any, method: str, args: list[Any], kwargs: dict[str, Any]
    ): ...


def _wrap_func(name, func):
    ty = get_type_hints(func)["return"]

    @wraps(func)
    async def wrapped(self, *args, **kwargs):
        return await self._rpc(ty, name, list(args), kwargs)

    return wrapped


def _proxy_protocol(protocol) -> Callable[[type[_RPC]], type]:
    """A class decorator that implements the methods of a Protocol using the
    underlying RPC mechanism."""

    assert is_protocol(protocol)

    def wrap(cls):
        for fn in get_protocol_members(protocol):
            if hasattr(cls, fn):
                continue
            func = getattr(protocol, fn)
            if not isinstance(func, FunctionType):
                raise AssertionError
            setattr(cls, fn, _wrap_func(fn, func))
        return type(cls.__name__, cls.__bases__, dict(cls.__dict__))

    return wrap


# ===============================================================
#  Server Code
# ===============================================================


@_proxy_protocol(RocqCursorProtocolAsync)
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


class WSMux:
    """This an asynchronous wrapper around a `WSConnection` and represents the client-side
    of a connection.

    This class and `WSServer` dictate the wire-level protocol which is
    the JSON representation of the `Request` and `Response` types defined
    at the top of this file. This is parametric over the interpretation of
    messages.

    NOTE: This class, and `WSServer` are likely implemented in other places
    as well, e.g. tinyrpc. We might want to switch to this library in the future.
    """

    _conn: WSConnection
    _fresh: int = -1
    _receiver: asyncio.Task[None]
    _futures: dict[int, asyncio.Future[tuple[bool, Any]]] = {}

    def __init__(self, conn: WSConnection):
        self._conn = conn

    async def start(self):
        self._receiver = asyncio.create_task(self._recv())

    async def stop(self):
        self._receiver.cancel()
        try:
            await self._receiver
        except asyncio.CancelledError:
            pass

    async def _recv(self) -> None:
        try:
            while True:
                resp_bytes = await self._conn.recv(decode=False)
                resp_json = json.loads(resp_bytes)
                resp = decoder.decode(resp_json, Response)
                match self._futures.pop(resp.id):
                    case None:
                        # TODO error handling?
                        pass
                    case future:
                        future.set_result((resp.is_exception, resp.payload))
        except websockets.ConnectionClosedOK:
            pass
        except websockets.ConnectionClosedError:
            # TODO
            pass

    async def send(
        self, method: str, args: list[Any], kwargs: dict[str, Any]
    ) -> tuple[bool, Any]:
        self._fresh += 1
        id = self._fresh
        req = Request(id=id, method=method, args=args, kwargs=kwargs)
        loop = asyncio.get_running_loop()
        future = loop.create_future()
        self._futures[id] = future
        try:
            req_encoded = encoder.encode(req)
            await self._conn.send(req_encoded)
        except websockets.ConnectionClosedOK:
            future.set_exception(ClosedOK())
        except websockets.ConnectionClosedError:
            future.set_exception(ClosedError())
            # TODO
            pass
        return await future


# ===============================================================
#  Client Code
# ===============================================================


class Dispatcher(Protocol):
    """Dispatchers capture a JSON-RPC-style protocol.
    They interpret methods given arguments and keyword arguments.
    """

    async def dispatch(
        self, method: str, args: list[Any], kwargs: dict[str, Any]
    ) -> Any:
        pass


class NamespaceDispatcher(Dispatcher):
    _dispatchers: dict[str, Dispatcher]

    def __init__(self, dispatchers: dict[str, Dispatcher]):
        self._dispatchers = dispatchers

    @override
    async def dispatch(
        self, method: str, args: list[Any], kwargs: dict[str, Any]
    ) -> Any:
        try:
            [ns, ns_method] = method.split("/", 1)
        except ValueError as e:
            # Since this is communicated back to the caller, it may
            # not make sense to propagate e
            raise ValueError(f"Unsupported method: '{method}'") from e
        if ns in self._dispatchers:
            return await self._dispatchers[ns].dispatch(ns_method, args, kwargs)


class WSServer:
    """A WSServer provides a dispatch loop for an asynchronous server.
    Clients will build a `Dispatcher` for the appropriate protocol and
    then pass it to this object to serve the protocol.
    """

    _conn: WSConnection
    _receiver: asyncio.Task[None]
    _futures: dict[int, asyncio.Future] = {}
    _dispatch: Dispatcher

    """We cannot use the generic type [T_inv] in the call to [decode.decode] in
    [_recv] because the type variable is not instantiated at runtime."""

    def __init__(self, conn: WSConnection, dispatcher: Dispatcher):
        self._conn = conn
        self._dispatch = dispatcher

    async def serve(self):
        self._receiver = asyncio.create_task(self._recv())
        await self._receiver

    async def stop(self):
        self._receiver.cancel()
        try:
            await self._receiver
        except asyncio.CancelledError:
            pass

    async def _handle_del(self, id, method, args: list[Any], kwargs: dict[str, Any]):
        is_exception = False
        try:
            result = await self._dispatch.dispatch(method, args, kwargs)
        except Exception as e:
            # print(f"RPC call to {method}: failed with {repr(e)} : {type(e)}")
            is_exception = True
            result = e
        try:
            payload = encoder.encode(result)
        except Exception as e:
            print(f"encoding of response {result} failed with {e}")
            raise e from e
        resp = Response(id=id, is_exception=is_exception, payload=payload)
        await self._conn.send(encoder.encode(resp))
        del self._futures[id]

    async def _recv(self):
        try:
            while True:
                req_bytes = await self._conn.recv(decode=False)
                req_json = json.loads(req_bytes)
                # print(f"req: {req_json}")
                try:
                    req = decoder.decode(req_json, Request)
                except Exception as e:
                    print(
                        f"Decoding of request {req_json} failed with: {repr(e)} : {type(e)}"
                    )
                    raise e from e
                future = asyncio.create_task(
                    self._handle_del(req.id, req.method, req.args, req.kwargs)
                )
                self._futures[req.id] = future
        except websockets.ConnectionClosedOK:
            pass
        except websockets.ConnectionClosedError:
            # TODO
            pass


class CursorDispatcher(Dispatcher):
    """This is a multi-dispatcher over `RocqCursorProtocol`.

    The first positional argument in each request is the cursor
    identifier. All of the other arguments are passed through to
    the corresponding cursor.
    """

    _cursors: dict[CursorId, RocqCursorProtocol]
    _fresh: int

    def __init__(self, cursors: dict[CursorId, RocqCursorProtocol]):
        self._cursors = cursors
        self._fresh = max([c.cursor for c in cursors])

    def extract_cursor(self, args: list[Any]) -> tuple[RocqCursorProtocol, list[Any]]:
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

from __future__ import annotations

import asyncio
import json
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
)

import websockets

from .deserialize import Decoder, EncoderProtocol
from .dispatcher import Dispatcher


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


def proxy_protocol(protocol) -> Callable[[type[_RPC]], type]:
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

    def __init__(
        self,
        conn: WSConnection,
        dispatcher: Dispatcher,
        encoder: EncoderProtocol,
        decoder: Decoder,
    ):
        self._encoder = encoder
        self._decoder = decoder
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
            payload = self._encoder.encode(result)
        except Exception as e:
            print(f"encoding of response {result} failed with {e}")
            raise e from e
        resp = Response(id=id, is_exception=is_exception, payload=payload)
        await self._conn.send(self._encoder.encode(resp))
        del self._futures[id]

    async def _recv(self):
        try:
            while True:
                req_bytes = await self._conn.recv(decode=False)
                req_json = json.loads(req_bytes)
                # print(f"req: {req_json}")
                try:
                    req = self._decoder.decode(req_json, Request)
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


# ===============================================================
#  Client Code
# ===============================================================


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
    closed_ok_exc: type[Exception]
    closed_err_exc: type[Exception]

    def __init__(
        self,
        conn: WSConnection,
        encoder: EncoderProtocol,
        decoder: Decoder,
        *,
        closed_ok: type[Exception] = Exception,
        closed_err: type[Exception] = Exception,
    ):
        self._encoder = encoder
        self._decoder = decoder
        self._conn = conn
        self.closed_err_exc = closed_err
        self.closed_ok_exc = closed_ok

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
                resp = self._decoder.decode(resp_json, Response)
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
            req_encoded = self._encoder.encode(req)
            await self._conn.send(req_encoded)
        except websockets.ConnectionClosedOK:
            future.set_exception(self.closed_ok_exc())
        except websockets.ConnectionClosedError:
            future.set_exception(self.closed_err_exc())
            # TODO
            pass
        return await future

from __future__ import annotations

import asyncio
from collections.abc import AsyncIterator, Awaitable, Callable
from contextlib import asynccontextmanager
from dataclasses import dataclass
from typing import Any, Literal, Protocol

from dataclasses_json import dataclass_json
from websockets import ConnectionClosed

from .protocol import Backend
from .types import Err, Resp


@dataclass_json
@dataclass
class Request:
    kind: Literal["request", "notification"]
    id: int
    method: str
    params: list[Any]


@dataclass_json
@dataclass
class Response[T, E]:
    id: int
    payload: Resp[T] | Err[E]


class WSConnection(Protocol):
    async def send(self, message: bytes) -> None: ...
    async def recv(self, decode: Literal[False]) -> bytes: ...


class WebsocketToBackend:
    """Forwards requests from a websocket connection to an existing
    Backend and relays responses back.

    Example use in a server:
    > backend = Process(...)
    > async with websockets.serve(WebsocketToBackend.make_handler(backend), ...):
    >    ...

    Example use in a client:
    > backed = Process(...)
    > async with websockets.connect(...) as conn:
    >     ws2b = WebsocketToBackend(backend, conn)
    >     asyncio.create_task(ws2b.loop())
    """

    _backend: Backend
    _conn: WSConnection
    _receiver: asyncio.Task[None]
    _sender: asyncio.Task[None]

    def __init__(self, backend: Backend, conn: WSConnection):
        self._backend = backend
        self._conn = conn
        self._receiver = asyncio.create_task(self._recv())
        self._sender = asyncio.create_task(self._send())

    async def _recv(self):
        while True:
            packet = await self._conn.recv(decode=False)
            await self._backend.send(packet)

    async def _send(self):
        while True:
            packet = await self._backend.recv()
            await self._conn.send(packet)

    async def loop(self) -> None:
        try:
            await asyncio.gather(self._receiver, self._sender)
        except asyncio.CancelledError:
            pass
        except ConnectionClosed:
            pass

    @asynccontextmanager
    @classmethod
    async def forward(
        cls, backend: Backend, conn: WSConnection
    ) -> AsyncIterator[asyncio.Task]:
        inst = WebsocketToBackend(backend, conn)
        task = asyncio.create_task(inst.loop())
        yield task
        inst._receiver.cancel("Shutdown")
        inst._sender.cancel("Shutdown")
        await task

    @classmethod
    def make_handler(
        cls, backend: Backend
    ) -> Callable[[WSConnection], Awaitable[None]]:
        return lambda conn: cls(backend, conn).loop()


class ProxyBackend(Backend):
    """A backend that directly forwards requests to and responses from a
    websocket client connection."""

    _conn: WSConnection

    def __init__(self, conn: WSConnection):
        self._conn = conn

    async def send(self, payload: bytes) -> None:
        await self._conn.send(payload)

    async def recv(self) -> bytes:
        return await self._conn.recv(decode=False)

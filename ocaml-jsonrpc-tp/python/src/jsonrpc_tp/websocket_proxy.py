from __future__ import annotations

import asyncio
from dataclasses import dataclass
from typing import Any, Literal

from dataclasses_json import dataclass_json
from websockets import ClientConnection, ServerConnection

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


class Handler:
    """Internal class that forwards requests from a websocket server connection
    to an existing Backend and relays responses back."""

    _backend: Backend
    _conn: ServerConnection
    _receiver: asyncio.Task[None]
    _sender: asyncio.Task[None]

    def __init__(self, backend: Backend, conn: ServerConnection):
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

    async def handle(self) -> None:
        await asyncio.gather(self._receiver, self._sender)


class Handlers:
    """Handlers connects an existing backend to a websocket server, forwarding
    requests that are sent to the websocket server to the backend and relaying
    responses from the backend through the server to clients.

    Use as follows:
    > handlers = Handlers(backend)
    > with websockets.serve(Handlers.handle, ...):
    >     ...
    """

    _backend: Backend

    def __init__(self, backend: Backend) -> None:
        self._backend = backend

    async def handle(self, conn: ServerConnection) -> None:
        handler = Handler(self._backend, conn)
        await handler.handle()


class ProxyBackend(Backend):
    """A backend that directly forwards requests to and responses from a
    websocket client connection."""

    _conn: ClientConnection

    def __init__(self, conn: ClientConnection):
        self._conn = conn

    async def send(self, payload: bytes) -> None:
        await self._conn.send(payload)

    async def recv(self) -> bytes:
        return await self._conn.recv(decode=False)

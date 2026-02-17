from __future__ import annotations

import asyncio
import json
from typing import Any

import websockets

from .deserialize import Decoder, EncoderProtocol
from .dispatcher import Dispatcher
from .tunnel import Request, Response


class DuplexMux:
    """Full-duplex micro RPC over a single WebSocket.

    - Outbound calls use `send(method, args, kwargs)` and await a Response.
    - Inbound Requests are dispatched via the provided `Dispatcher`.

    Wire format is the JSON encoding of `Request` / `Response`.
    """

    def __init__(
        self,
        conn: Any,
        *,
        dispatcher: Dispatcher,
        encoder: EncoderProtocol,
        decoder: Decoder,
    ) -> None:
        self._conn = conn
        self._dispatcher = dispatcher
        self._encoder = encoder
        self._decoder = decoder

        self._fresh: int = -1
        self._pending: dict[int, asyncio.Future[tuple[bool, Any]]] = {}
        self._receiver: asyncio.Task[None] | None = None
        self._closed = asyncio.Event()

    async def start(self) -> None:
        if self._receiver is not None:
            return
        self._receiver = asyncio.create_task(self._recv_loop())

    async def stop(self) -> None:
        self._closed.set()
        if self._receiver is not None:
            self._receiver.cancel()
            await asyncio.gather(self._receiver, return_exceptions=True)
            self._receiver = None
        for fut in list(self._pending.values()):
            if not fut.done():
                fut.set_exception(ConnectionError("connection closed"))
        self._pending.clear()

    async def send(
        self,
        method: str,
        args: list[Any] | None = None,
        kwargs: dict[str, Any] | None = None,
    ) -> tuple[bool, Any]:
        if self._closed.is_set():
            raise ConnectionError("connection closed")
        args = [] if args is None else args
        kwargs = {} if kwargs is None else kwargs

        self._fresh += 1
        req_id = self._fresh
        loop = asyncio.get_running_loop()
        fut: asyncio.Future[tuple[bool, Any]] = loop.create_future()
        self._pending[req_id] = fut

        req = Request(id=req_id, method=method, args=args, kwargs=kwargs)
        await self._conn.send(self._encoder.encode(req))
        return await fut

    async def _handle_request(self, req: Request) -> None:
        is_exception = False
        try:
            result = await self._dispatcher.dispatch(req.method, req.args, req.kwargs)
        except Exception as e:
            is_exception = True
            result = e

        payload = self._encoder.encode(result)
        resp = Response(id=req.id, is_exception=is_exception, payload=payload)
        await self._conn.send(self._encoder.encode(resp))

    async def _recv_loop(self) -> None:
        try:
            while not self._closed.is_set():
                raw = await self._conn.recv(decode=False)
                msg_json = json.loads(raw)

                ty = msg_json.get("_ty")
                if ty == "Response":
                    resp = self._decoder.decode(msg_json, Response)
                    fut = self._pending.pop(resp.id, None)
                    if fut is not None and not fut.done():
                        fut.set_result((resp.is_exception, resp.payload))
                    continue

                if ty == "Request":
                    req = self._decoder.decode(msg_json, Request)
                    asyncio.create_task(self._handle_request(req))
                    continue
        except websockets.ConnectionClosedOK:
            return
        except websockets.ConnectionClosedError:
            return
        except Exception as e:
            for fut in list(self._pending.values()):
                if not fut.done():
                    fut.set_exception(e)
            self._pending.clear()
        finally:
            self._closed.set()

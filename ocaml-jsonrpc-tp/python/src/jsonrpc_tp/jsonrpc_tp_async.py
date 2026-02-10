from __future__ import annotations  # noqa:I001

import asyncio
import json
from collections.abc import AsyncIterator
from contextlib import asynccontextmanager
from typing import (
    Any,
    Self,
)
from collections.abc import Awaitable
from collections.abc import Callable

from .types import Err, Error, Resp, parse_response, parse_notification
from .protocol import Backend


class AsyncJsonRPCTP:
    """JSON-RPC interface relied on by the jsonrpc-tp OCaml package."""

    _backend: Backend
    _counter: int
    _notification_handler: Callable[[str, dict[str, Any]], Awaitable[None]] | None
    _handlers: asyncio.Queue[asyncio.Task] = asyncio.Queue()
    _send_queue: asyncio.Queue[bytes] = asyncio.Queue()
    _pending_requests: dict[int, asyncio.Future[Resp[Any] | Err[Any]]] = {}
    _running: bool

    def __init__(
        self,
        backend: Callable[[], Backend],
        handle_notification: Callable[[str, dict[str, Any]], Awaitable[None]]
        | None = None,
    ) -> None:
        self._counter: int = -1
        self._backend = backend()
        self._notification_handler: (
            Callable[[str, dict[str, Any]], Awaitable[None]] | None
        ) = handle_notification
        # Handlers for notifications.
        self._handlers: asyncio.Queue[asyncio.Task] = asyncio.Queue()
        self._send_queue: asyncio.Queue[bytes] = asyncio.Queue()
        self._pending_requests: dict[int, asyncio.Future[Resp[Any] | Err[Any]]] = {}
        self._running: bool = True
        self._sender_task = asyncio.create_task(self._sender_loop())
        self._receiver_task = asyncio.create_task(self._receiver_loop())
        self._handlers_task = asyncio.create_task(self._handlers_loop())

    async def raw_notification(
        self,
        method: str,
        params: list[Any],
    ) -> None:
        self._check_running()
        notification = json.dumps(
            {"jsonrpc": "2.0", "method": method, "params": params}
        ).encode()
        await self._send_queue.put(notification)

    async def raw_request(
        self,
        method: str,
        params: list[Any],
    ) -> Resp[Any] | Err[Any]:
        self._check_running()
        # Getting a fresh request id.
        self._counter = self._counter + 1
        fresh_id = self._counter
        # Preparing and sending the request.
        request = json.dumps(
            {"jsonrpc": "2.0", "method": method, "params": params, "id": fresh_id}
        ).encode()
        # creating the future, and registering it for the receiver loop.
        loop = asyncio.get_running_loop()
        future = loop.create_future()
        self._pending_requests[fresh_id] = future
        await self._send_queue.put(request)
        response = await future
        return response

    @asynccontextmanager
    async def sess(self) -> AsyncIterator[Self]:
        """Context manager that calls quit upon __exit__."""
        yield self
        await self.quit()

    async def quit(self) -> None:
        self._check_running()
        # Stop any further requests.
        self._running = False
        # Make sure we send all the requests in the queue.
        self._send_queue.shutdown(immediate=False)
        await self._send_queue.join()
        await self._backend.quit()
        if not self._sender_task.done():
            self._sender_task.cancel("Shutdown")
        if not self._receiver_task.done():
            self._receiver_task.cancel("Shutdown")
        try:
            await self._sender_task
            await self._receiver_task
        except asyncio.CancelledError:
            pass
        # Wait for the notification handlers
        self._handlers.shutdown(immediate=False)
        await self._handlers.join()
        await self._handlers_task

    def _check_running(self) -> None:
        if not self._running:
            raise Error("Process has been stopped or is stopping.")

    async def _sender_loop(self) -> None:
        """Reads from send queue, sends the raw packets."""
        try:
            while True:
                packet = await self._send_queue.get()
                await self._send(packet)
                self._send_queue.task_done()
        except asyncio.QueueShutDown:
            pass
        except Exception as e:
            raise Exception(f"Sender error: {e}") from e

    async def _handle_response(self, response: Any) -> None:
        req_id = response.get("id")
        future = self._pending_requests.pop(req_id)
        try:
            r = parse_response(response)
            future.set_result(r)
        except Exception as e:
            future.set_exception(e)

    async def _handle_notification(self, notification: Any) -> None:
        method, params = parse_notification(notification)
        if self._notification_handler:

            async def handler():
                try:
                    await self._notification_handler(method, params)
                except Exception:
                    pass

            await self._handlers.put(asyncio.create_task(handler()))

    async def _receiver_loop(self):
        """Task 2: Reads from network, dispatches to waiting futures."""
        try:
            while True:
                packet = await self._recv()

                if "error" in packet or "result" in packet:
                    await self._handle_response(packet)
                elif isinstance(packet, list):
                    async for response in packet:
                        await self._handle_response(response)
                else:
                    await self._handle_notification(packet)
        except Exception as e:
            raise Exception(f"Receiver error: {e}") from e

    async def _handlers_loop(self) -> None:
        """Reads from the (notification) handler queue, and wait for tasks."""
        try:
            while True:
                task = await self._handlers.get()
                await task
                self._handlers.task_done()
        except asyncio.CancelledError:
            pass
        except asyncio.QueueShutDown:
            pass
        except Exception as e:
            raise Exception(f"Notification handler loop error: {e}") from e

    async def _send(self, req: bytes) -> None:
        await self._backend.send(req)

    async def _recv(self) -> Any:
        return json.loads(await self._backend.recv())

from __future__ import annotations  # noqa:I001

import asyncio
import json
from typing import (
    Any,
    Protocol,
)
from collections.abc import Awaitable
from collections.abc import Callable

from .jsonrpc_tp_types import Err, Error, Resp


class AsyncProtocol(Protocol):
    """Protocol for a asynchronous JSON-RPC API."""

    async def raw_notification(
        self,
        method: str,
        params: list[Any],
    ) -> None:
        """Send a JSON-RPC notification."""
        ...

    async def raw_request(
        self,
        method: str,
        params: list[Any],
    ) -> Resp[Any] | Err[Any]:
        """Send a JSON-RPC request."""
        ...

    async def quit(self) -> None:
        """Terminate the connection with the underlying "server"."""
        ...


class AsyncJsonRPCTP(AsyncProtocol):
    """JSON-RPC interface relied on by the jsonrpc-tp OCaml package."""

    def __init__(
        self,
        args: list[str],
        cwd: str | None = None,
        env: dict[str, str] | None = None,
        handle_notification: Callable[[str, dict[str, Any]], Awaitable[None]]
        | None = None,
    ) -> None:
        self._counter: int = -1
        self._args: list[str] = args
        self._cwd: str | None = cwd
        self._env: dict[str, str] | None = env
        self._notification_handler: (
            Callable[[str, dict[str, Any]], Awaitable[None]] | None
        ) = handle_notification
        # Handlers for notifications.
        self._handlers: asyncio.Queue[asyncio.Task] = asyncio.Queue()
        self._send_queue: asyncio.Queue[bytes] = asyncio.Queue()
        self._pending_requests: dict[int, asyncio.Future[Resp[Any] | Err[Any]]] = {}
        self._running: bool = True

    async def start(self) -> None:
        try:
            self._process = await asyncio.create_subprocess_exec(
                self._args[0],
                *self._args[1:],
                stdin=asyncio.subprocess.PIPE,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
                cwd=self._cwd,
                env=self._env,
            )
        except Exception as e:
            raise Error(f"Failed to start process: {e}") from e

        # Check the "ready_seq" notification
        try:
            ready = await self._recv()
            if "method" not in ready:
                raise Error(f"Unexpected packet: {ready} (not a notification)")
            method = ready.get("method")
            if method != "ready":
                raise Error(f'Got "{method}" notification instead of "ready"')
        except Exception as e:
            self._process.kill()
            raise Error(f"Failed to start JSON-RPC service: {e}") from e

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

    async def quit(self) -> None:
        self._check_running()
        # Stop any further requests.
        self._running = False
        # Make sure we send all the requests in the queue.
        self._send_queue.shutdown(immediate=False)
        await self._send_queue.join()
        await self._sender_task
        # Close the outgoing pipe.
        assert self._process.stdin is not None
        self._process.stdin.close()
        # Wait for the process.
        await self._process.wait()
        await self._receiver_task
        # Wait for the notification handlers
        self._handlers.shutdown(immediate=False)
        await self._handlers.join()
        await self._handlers_task

    def _check_running(self) -> None:
        if not self._running or not hasattr(self, "_process"):
            raise Error("Process has been stopped or is stopping.")

    async def _sender_loop(self) -> None:
        """Reads from send queue, sends the raw packets."""
        try:
            while True:
                packet = await self._send_queue.get()
                await self._send(packet)
                self._send_queue.task_done()
        except asyncio.CancelledError:
            pass
        except asyncio.QueueShutDown:
            pass
        except Exception as e:
            raise Exception(f"Sender error: {e}") from e

    async def _handle_response(self, response: Any) -> None:
        req_id = response.get("id")
        future = self._pending_requests.pop(req_id)

        if "error" in response:
            # Error response for the request.
            error = response.get("error")
            message = error.get("message")
            code = error.get("code")
            data = error.get("data", None)
            match code:
                # Request failed (taken from the LSP protocol)
                case -32803:
                    future.set_result(Err(message, data))
                # Method not found | Invalid params
                case -32601 | -32602:
                    future.set_exception(Exception(message))
                # Anything else is unexpected.
                case _:
                    future.set_exception(
                        Error(f"Unexpected error code {code}: {message}")
                    )
        elif "result" in response:
            # Normal response for the request.
            result = response.get("result")
            future.set_result(Resp(result))

    async def _handle_notification(self, notification: Any) -> None:
        # Notification.
        assert "method" in notification
        assert "id" not in notification
        method = notification.get("method")
        assert isinstance(method, str)
        params = notification.get("params", {})
        assert isinstance(params, dict)
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
        except asyncio.CancelledError:
            pass
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
        assert self._process.stdin is not None
        prefix = "Content-Length: "
        self._process.stdin.write(f"{prefix}{len(req) + 1}\r\n\r\n".encode())
        self._process.stdin.write(req)
        self._process.stdin.write(b"\n")
        await self._process.stdin.drain()

    async def _recv(self) -> Any:
        assert self._process.stdout is not None
        prefix = "Content-Length: "
        try:
            raw_header: bytes = await self._process.stdout.readuntil()
        except asyncio.IncompleteReadError as e:
            if not self._running and e.partial == b"":
                raise asyncio.CancelledError() from e
            raise
        header: str = raw_header.decode()
        _ = await self._process.stdout.readuntil()
        if not header.startswith(prefix):
            self._process.kill()
            raise Error(f"Invalid message header: '{header}'")
        try:
            nb_bytes = int(header[len(prefix) : -2])
        except Exception as e:
            self._process.kill()
            raise Error(f"Failed to parse header: {header}", e) from e
        assert self._process.stdout is not None
        response: bytes = await self._process.stdout.readexactly(nb_bytes)
        return json.loads(response.decode())

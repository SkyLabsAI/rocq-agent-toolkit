from __future__ import annotations  # noqa:I001

import asyncio
import json
import tempfile
from pathlib import Path
from typing import (
    Any,
    NoReturn,
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
        cwd: Path | str | None = None,
        env: dict[str, str] | None = None,
        handle_notification: Callable[[str, dict[str, Any]], Awaitable[None]]
        | None = None,
    ) -> None:
        self._counter: int = -1
        self._args: list[str] = args
        self._cwd: str | None = str(cwd) if cwd is not None else None
        self._env: dict[str, str] | None = env
        self._stderr = tempfile.TemporaryFile(mode="w+t")
        self._notification_handler: (
            Callable[[str, dict[str, Any]], Awaitable[None]] | None
        ) = handle_notification
        # Handlers for notifications.
        self._handlers: asyncio.Queue[asyncio.Task] = asyncio.Queue()
        self._send_queue: asyncio.Queue[bytes] = asyncio.Queue()
        self._pending_requests: dict[int, asyncio.Future[Resp[Any] | Err[Any]]] = {}
        self._started: bool = False
        self._running: bool = False

    async def start(self) -> None:
        try:
            self._process = await asyncio.create_subprocess_exec(
                self._args[0],
                *self._args[1:],
                stdin=asyncio.subprocess.PIPE,
                stdout=asyncio.subprocess.PIPE,
                stderr=self._stderr,
                cwd=self._cwd,
                env=self._env,
            )
        except Exception as e:
            raise Error(f"Failed to start process: {e}") from e

        # Gather the pipes.
        assert self._process.stdin is not None
        self._stdin: asyncio.streams.StreamWriter = self._process.stdin
        assert self._process.stdout is not None
        self._stdout: asyncio.streams.StreamReader = self._process.stdout

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
            self._error_with_stderr(f"Failed to start JSON-RPC service\n{e}", e)

        self._sender_task = asyncio.create_task(self._sender_loop())
        self._receiver_task = asyncio.create_task(self._receiver_loop())
        self._handlers_task = asyncio.create_task(self._handlers_loop())
        self._started = True
        self._running = True

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
        self._stdin.close()
        # Wait for the process.
        await self._process.wait()
        await self._receiver_task
        # Wait for the notification handlers
        self._handlers.shutdown(immediate=False)
        await self._handlers.join()
        await self._handlers_task

    def _cleanup(self) -> None:
        if not self._running:
            return
        self._running = False
        # Killing the process
        self._process.kill()
        # Cancelling the tasks.
        self._sender_task.cancel()
        self._receiver_task.cancel()
        self._handlers_task.cancel()
        # Shutting down the queues
        self._send_queue.shutdown(immediate=True)
        self._handlers.shutdown(immediate=True)
        # Answering the pending requests with an exception
        while self._pending_requests:
            req_id, future = self._pending_requests.popitem()
            future.set_exception(
                Error(f"Cannot complete request {req_id} (server shutdown)")
            )

    def _error_with_stderr(self, msg: str, e: Exception | None = None) -> NoReturn:
        self._stderr.seek(0)
        stderr_data = self._stderr.read()
        stderr = None if not stderr_data else stderr_data
        raise Error(msg, stderr=stderr) from e

    def _check_running(self) -> None:
        if not self._started:
            raise Error("Process has not started.")
        if not self._running:
            raise Error("Process has been stopped or is stopping.")

    async def _sender_loop(self) -> None:
        """Reads from send queue, sends the raw packets."""
        try:
            while True:
                packet = await self._send_queue.get()
                await self._send_packet(packet)
                self._send_queue.task_done()
        except asyncio.CancelledError:
            pass
        except asyncio.QueueShutDown:
            pass
        except Exception as e:
            self._cleanup()
            self._error_with_stderr(f"Unexpected sender error: {e}", e)

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
        self_notification = self._notification_handler
        if self_notification:

            async def handler() -> None:
                try:
                    await self_notification(method, params)
                except Exception:
                    pass

            await self._handlers.put(asyncio.create_task(handler()))

    async def _receiver_loop(self) -> None:
        """Task 2: Reads from network, dispatches to waiting futures."""
        try:
            while True:
                packet = await self._recv()

                if isinstance(packet, list):
                    for response in packet:
                        await self._handle_response(response)
                elif isinstance(packet, dict) and (
                    "error" in packet or "result" in packet
                ):
                    await self._handle_response(packet)
                else:
                    await self._handle_notification(packet)
        except asyncio.CancelledError:
            pass
        except Exception as e:
            self._cleanup()
            self._error_with_stderr(f"Unexpected receiver error: {e}", e)

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
            self._cleanup()
            self._error_with_stderr(f"Unexpected handler loop error: {e}", e)

    _prefix = "Content-Length: "

    async def _send_packet(self, packet: bytes) -> None:
        self._stdin.write(f"{self._prefix}{len(packet) + 1}\r\n\r\n".encode())
        self._stdin.write(packet)
        self._stdin.write(b"\n")
        try:
            await self._stdin.drain()
        except BrokenPipeError as e:
            self._cleanup()
            self._error_with_stderr("Cannot send packet (broken pipe)", e)

    async def _recv_packet(self) -> bytes:
        header_line_read = False
        try:
            # Input the header, and following empty line
            raw_header: bytes = await self._stdout.readuntil()
            header_line_read = True
            # Parsing the header
            header: str = raw_header.decode()
            if not header.startswith(self._prefix) or not header.endswith("\r\n"):
                self._cleanup()
                self._error_with_stderr(f"Invalid packet header: '{header}'")
            try:
                nb_bytes = int(header[len(self._prefix) : -2])
            except ValueError as e:
                self._cleanup()
                self._error_with_stderr(f"Failed to parse header: '{header}'", e)
            # Reading and checking the "\r\n" separator
            crlf = await self._stdout.readexactly(2)
            if crlf != b"\r\n":
                self._cleanup()
                self._error_with_stderr("Invalid separator: '{crlf}'")
            # Reading and returning the packet
            packet = await self._stdout.readexactly(nb_bytes)
            return packet
        except asyncio.IncompleteReadError as e:
            # Special case used for shutdown
            if (
                not header_line_read
                and self._started
                and not self._running
                and e.partial == b""
            ):
                raise asyncio.CancelledError() from e
            self._cleanup()
            self._error_with_stderr("Could not read a full packet", e)
        except asyncio.LimitOverrunError as e:
            self._cleanup()
            self._error_with_stderr("Ill-formed header (way too long)", e)
        except BrokenPipeError as e:
            self._cleanup()
            self._error_with_stderr("Cannot receive packet (broken pipe)", e)
        except UnicodeDecodeError as e:
            self._cleanup()
            self._error_with_stderr(f"Invalid unicode in header: {e.reason}", e)

    async def _recv(self) -> Any:
        packet = await self._recv_packet()
        try:
            return json.loads(packet.decode())
        except UnicodeDecodeError as e:
            self._cleanup()
            self._error_with_stderr(f"Invalid unicode in packet: {e.reason}", e)
        except json.JSONDecodeError as e:
            self._cleanup()
            self._error_with_stderr(f"Invalid JSON in packet: {e.msg}.", e)

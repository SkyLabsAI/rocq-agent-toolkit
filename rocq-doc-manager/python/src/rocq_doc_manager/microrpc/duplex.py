from __future__ import annotations

import asyncio
import json
from typing import Literal, Protocol, overload, override

from pydantic import JsonValue

from .dispatcher import Dispatcher


class PacketChannel(Protocol):
    """A packet-based channel."""

    @overload
    async def send(self, message: bytes) -> None: ...
    @overload
    async def send(self, message: str) -> None: ...
    async def recv(self, decode: Literal[False]) -> bytes: ...
    async def close(self) -> None: ...


class RPCClient(Protocol):
    async def send(
        self, method: str, params: JsonValue | None = None
    ) -> tuple[bool, JsonValue]:
        """
        Returns (success, result):
            success -- if the value is an exception
            result -- the result, should be interpreted based on success
        """
        ...


# TODO: how is this related to WSMux
class DuplexMux(RPCClient):
    """Full-duplex micro RPC over a single WebSocket.

    - Outbound calls use `send(method, args, kwargs)` and await a Response.
    - Inbound Requests are dispatched via the provided `Dispatcher`.

    Wire format is the JSON encoding of `Request` / `Response`.
    """

    def __init__(
        self,
        conn: PacketChannel,
        *,
        dispatcher: Dispatcher,
    ) -> None:
        self._conn = conn
        self._dispatcher = dispatcher

        self._fresh: int = -1
        self._pending: dict[int | str, asyncio.Future[tuple[bool, JsonValue]]] = {}
        self._receiver: asyncio.Task[None] | None = None
        self._closed = asyncio.Event()

    def handle_error(self, exc: Exception) -> None:
        """This can be overridden by clients that want to track errors"""
        pass

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

    @override
    async def send(
        self,
        method: str,
        params: JsonValue | None = None,
    ) -> tuple[bool, JsonValue]:
        if self._closed.is_set():
            raise ConnectionError("connection closed")

        self._fresh += 1
        req_id = self._fresh
        loop = asyncio.get_running_loop()
        fut: asyncio.Future[tuple[bool, JsonValue]] = loop.create_future()
        self._pending[req_id] = fut

        # req = Request(id=req_id, method=method, args=args, kwargs=kwargs)
        req: dict[str, JsonValue] = {"jsonrpc": "2.0", "method": method, "id": req_id}
        if params is not None:
            req["params"] = params
        await self._conn.send(json.dumps(req))
        return await fut

    async def notify(
        self,
        method: str,
        params: JsonValue | None = None,
    ) -> None:
        if self._closed.is_set():
            raise ConnectionError("connection closed")

        # Notifications do not carry request identifiers
        req: dict[str, JsonValue] = {"jsonrpc": "2.0", "method": method}
        if params is not None:
            req["params"] = params
        await self._conn.send(json.dumps(req))

    async def _handle_request(
        self, id: int | str | None, method: str, params: JsonValue | None
    ) -> None:
        is_success = False
        try:
            is_success, result = await self._dispatcher.dispatch(method, params)
        except Exception as e:
            self.handle_error(e)
            return

        response: dict[str, JsonValue] = {
            "jsonrpc": "2.0",
        }
        if id is not None:
            response["id"] = id
        if is_success:
            response["error"] = result
        else:
            response["result"] = result
        await self._conn.send(json.dumps(response))

    async def _recv_loop(self) -> None:
        try:
            while not self._closed.is_set():
                raw = await self._conn.recv(decode=False)
                try:
                    msg_json = json.loads(raw)
                except json.JSONDecodeError as err:
                    self.handle_error(err)
                    continue

                if "jsonrpc" not in msg_json or msg_json["jsonrpc"] != "2.0":
                    self.handle_error(
                        KeyError(f"Missing 'jsonrpc' field in {msg_json}")
                    )
                    continue

                has_result = "result" in msg_json
                has_error = "error" in msg_json
                if has_result and has_error:
                    self.handle_error(
                        ValueError(
                            f"Ambiguous response contains both 'result' and 'error': {msg_json}"
                        )
                    )
                    continue
                elif has_result or has_error:
                    if "id" not in msg_json:
                        self.handle_error(
                            KeyError(f"Missing 'id' field in response: {msg_json}")
                        )
                        continue
                    if not isinstance(msg_json["id"], int) and not isinstance(
                        msg_json["id"], str
                    ):
                        self.handle_error(
                            ValueError(f"Invalid 'id' field in response: {msg_json}")
                        )
                        continue
                    try:
                        fut = self._pending.pop(msg_json["id"], None)
                    except KeyError:
                        self.handle_error(
                            ValueError(f"Invalid 'id' field in response: {msg_json}")
                        )
                        continue
                    if fut is not None and not fut.done():
                        if has_result:
                            fut.set_result((True, msg_json["result"]))
                        else:
                            fut.set_result((False, msg_json["error"]))
                    else:
                        self.handle_error(
                            ValueError(
                                f"Recieved multiple responses for id={msg_json['id']}: {msg_json}"
                            )
                        )

                else:
                    # This must be a request
                    if "method" not in msg_json:
                        self.handle_error(
                            KeyError(f"Missing 'method' field in request: {msg_json}")
                        )
                        continue
                    method = msg_json["method"]
                    if not isinstance(method, str):
                        self.handle_error(
                            ValueError(
                                f"Invalid 'method' field in request (must be string): {msg_json}"
                            )
                        )
                        continue
                    id: int | str | None = None
                    if "id" in msg_json:
                        if isinstance(msg_json["id"], int) or isinstance(
                            msg_json["id"], str
                        ):
                            id = msg_json["id"]
                        else:
                            self.handle_error(
                                ValueError(
                                    f"Invalid 'id' field in request (must be integer): {msg_json}"
                                )
                            )
                            continue

                    asyncio.create_task(
                        self._handle_request(
                            id=id,
                            method=method,
                            params=msg_json["params"] if "params" in msg_json else None,
                        )
                    )
        # except websockets.ConnectionClosedOK:
        #     return
        # except websockets.ConnectionClosedError:
        #     return
        except Exception as e:
            for fut in list(self._pending.values()):
                if not fut.done():
                    fut.set_exception(e)
            self._pending.clear()
        finally:
            self._closed.set()

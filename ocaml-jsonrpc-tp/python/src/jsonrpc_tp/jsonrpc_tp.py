import json
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from typing import (
    Any,
    Self,
)

from .protocol import Backend
from .types import Err, Error, Resp, parse_notification, parse_response


class JsonRPCTP:
    """JSON-RPC interface relied on by the jsonrpc-tp OCaml package."""

    _backend: Backend | None

    def __init__(self, backend: Backend) -> None:
        self._backend = backend
        self._counter: int = -1

    @contextmanager
    def sess(self) -> Iterator[Self]:
        """Context manager that calls quit upon __exit__."""
        yield self
        self.quit()

    @contextmanager
    def backend(self) -> Iterator[Backend]:
        if self._backend is None:
            raise Error("Not running anymore.")
        yield self._backend

    def quit(self) -> None:
        if self._backend is None:
            return
        self._backend = None

    def send(self, req: bytes) -> None:
        with self.backend() as backend:
            backend.send_sync(req)

    def recv(self) -> Any:
        with self.backend() as backend:
            return json.loads(backend.recv_sync())

    def raw_notification(
        self,
        method: str,
        params: list[Any],
    ) -> None:
        notification = json.dumps(
            {"jsonrpc": "2.0", "method": method, "params": params}
        ).encode()
        self.send(notification)

    def raw_request(
        self,
        method: str,
        params: list[Any],
        handle_notification: Callable[[str, dict[str, Any]], None] | None = None,
    ) -> Resp[Any] | Err[Any]:
        # Getting a fresh request id.
        self._counter = self._counter + 1
        fresh_id = self._counter
        # Preparing and sending the request.
        req = json.dumps(
            {"jsonrpc": "2.0", "method": method, "params": params, "id": fresh_id}
        ).encode()
        self.send(req)
        # Reading the response.
        while True:
            packet = self.recv()
            if "error" in packet or "result" in packet:
                return parse_response(packet)
            elif isinstance(packet, list):
                raise Error("Batch responses not supported.")
            else:
                noti = parse_notification(packet)
                if handle_notification is not None:
                    handle_notification(*noti)

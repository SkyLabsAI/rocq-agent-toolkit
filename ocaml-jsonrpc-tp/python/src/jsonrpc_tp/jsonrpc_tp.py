import json
import subprocess
from collections.abc import Callable
from typing import (
    Any,
    Protocol,
)

from .jsonrpc_tp_types import Err, Error, Resp


class SyncProtocol(Protocol):
    """Protocol for a synchronous JSON-RPC API."""

    def raw_notification(
        self,
        method: str,
        params: list[Any],
    ) -> None:
        """Send a JSON-RPC notification."""
        ...

    def raw_request(
        self,
        method: str,
        params: list[Any],
        handle_notification: Callable[[str, dict[str, Any]], None] | None = None,
    ) -> Resp[Any] | Err[Any]:
        """Send a JSON-RPC request."""
        ...

    def quit(self) -> None:
        """Terminate the connection with the underlying "server"."""
        ...


def _read_exactly(stream, nb_bytes: int) -> bytes:
    buf = bytearray(nb_bytes)
    view = memoryview(buf)
    bytes_received = 0
    while bytes_received < nb_bytes:
        n = stream.readinto(view[bytes_received:])
        if n == 0:
            raise Error(
                f"End of file reached with {bytes_received}/{nb_bytes} bytes received."
            )
        bytes_received += n
    return bytes(buf)


class JsonRPCTP(SyncProtocol):
    """JSON-RPC interface relied on by the jsonrpc-tp OCaml package."""

    def __init__(
        self, args: list[str], cwd: str | None = None, env: dict[str, str] | None = None
    ) -> None:
        self._process: subprocess.Popen | None = None
        self._counter: int = -1

        try:
            self._process = subprocess.Popen(
                args,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                cwd=cwd,
                env=env,
            )
        except Exception as e:
            self._process = None
            raise Error(f"Failed to start process: {e}") from e

        # Check the "ready_seq" notification
        try:
            ready = self.recv()
            if "method" not in ready:
                raise Error(f"Unexpected packet: {ready} (not a notification)")
            method = ready.get("method")
            if method != "ready_seq":
                raise Error(f'Got "{method}" notification instead of "ready_seq"')
        except Exception as e:
            if self._process is not None:
                # [recv] often sets `self._process` to None when there is an error
                self._process.kill()
                self._process = None
            raise Error(f"Failed to start JSON-RPC service: {e}") from e

    def send(self, req: bytes) -> None:
        if self._process is None:
            raise Error("Not running anymore.")
        assert self._process.stdin is not None
        prefix = "Content-Length: "
        self._process.stdin.write(f"{prefix}{len(req) + 1}\r\n\r\n".encode())
        self._process.stdin.write(req)
        self._process.stdin.write(b"\n")
        self._process.stdin.flush()

    def recv(self) -> Any:
        if self._process is None:
            raise Error("Not running anymore.")
        assert self._process.stdout is not None
        prefix = "Content-Length: "
        header: str = self._process.stdout.readline().decode()
        _ = self._process.stdout.readline()
        if not header.startswith(prefix):
            self._process.kill()
            self._process = None
            raise Error(f"Invalid message header: '{header}'")
        try:
            nb_bytes = int(header[len(prefix) : -2])
        except Exception as e:
            self._process.kill()
            self._process = None
            raise Error(f"Failed to parse header: {header}", e) from e
        assert self._process.stdout is not None
        response = _read_exactly(self._process.stdout, nb_bytes).decode()
        return json.loads(response)

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
            response = self.recv()
            if "error" in response:
                # Error response for the request.
                error = response.get("error")
                message = error.get("message")
                code = error.get("code")
                match code:
                    # Request failed (taken from the LSP protocol)
                    case -32803:
                        return Err(message, error.get("data"))
                    # Method not found | Invalid params
                    case -32601 | -32602:
                        raise Exception(message)
                    # Anything else is unexpected.
                    case _:
                        raise Error(f"Unexpected error code {code} ({message})")
            elif "result" in response:
                # Normal response for the request.
                return Resp(response.get("result"))
            else:
                # Notification.
                assert "method" in response
                method = response.get("method")
                assert isinstance(method, str)
                params = response.get("params", {})
                assert isinstance(params, dict)
                if handle_notification:
                    handle_notification(method, params)

    def quit(self) -> None:
        if self._process is None:
            return
        assert self._process.stdin is not None
        self._process.stdin.close()
        self._process.wait()
        self._process = None

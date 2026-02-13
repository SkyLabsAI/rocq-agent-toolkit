import json
import subprocess
import tempfile
from collections.abc import Callable
from typing import IO, Any, Protocol

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
        self._stderr = tempfile.TemporaryFile(mode="w+t")

        try:
            self._process = subprocess.Popen(
                args,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=self._stderr,
                cwd=cwd,
                env=env,
            )
        except Exception as e:
            self._process = None
            raise Error(f"Failed to start process: {e}") from e

        # Gather the pipes.
        assert self._process.stdin is not None
        self._stdin: IO[bytes] = self._process.stdin
        assert self._process.stdout is not None
        self._stdout: IO[bytes] = self._process.stdout

        # Check the "ready_seq" notification
        try:
            ready = self._recv()
            if "method" not in ready:
                raise Error(f"Unexpected packet: {ready} (not a notification)")
            method = ready.get("method")
            if method != "ready_seq":
                raise Error(f'Got "{method}" notification instead of "ready_seq"')
        except Exception as e:
            self._kill_process()
            self._stderr.seek(0)
            stderr_data = self._stderr.read()
            stderr = None if not stderr_data else stderr_data
            raise Error(f"Failed to start JSON-RPC service: {e}", stderr=stderr) from e

    def __del__(self) -> None:
        if self._process is not None:
            self.quit()

    def raw_notification(
        self,
        method: str,
        params: list[Any],
    ) -> None:
        self._check_running()
        notification = json.dumps(
            {"jsonrpc": "2.0", "method": method, "params": params}
        ).encode()
        self._send(notification)

    def raw_request(
        self,
        method: str,
        params: list[Any],
        handle_notification: Callable[[str, dict[str, Any]], None] | None = None,
    ) -> Resp[Any] | Err[Any]:
        self._check_running()
        # Getting a fresh request id.
        self._counter = self._counter + 1
        fresh_id = self._counter
        # Preparing and sending the request.
        req = json.dumps(
            {"jsonrpc": "2.0", "method": method, "params": params, "id": fresh_id}
        ).encode()
        self._send(req)
        # Reading the response.
        while True:
            response = self._recv()
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
        self._check_running()
        assert self._process is not None
        self._stdin.close()
        self._process.wait()
        self._process = None

    def _check_running(self) -> None:
        if self._process is None:
            raise Error("Not running anymore.")

    def _kill_process(self) -> None:
        if self._process is not None:
            self._process.kill()
            self._process = None

    def _send(self, req: bytes) -> None:
        prefix = "Content-Length: "
        self._stdin.write(f"{prefix}{len(req) + 1}\r\n\r\n".encode())
        self._stdin.write(req)
        self._stdin.write(b"\n")
        self._stdin.flush()

    def _recv(self) -> Any:
        prefix = "Content-Length: "
        header: str = self._stdout.readline().decode()
        _ = self._stdout.readline()
        if not header.startswith(prefix):
            self._kill_process()
            raise Error(f"Invalid message header: '{header}'")
        try:
            nb_bytes = int(header[len(prefix) : -2])
        except Exception as e:
            self._kill_process()
            raise Error(f"Failed to parse header: {header}", e) from e
        response = _read_exactly(self._stdout, nb_bytes).decode()
        return json.loads(response)

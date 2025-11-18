from contextlib import contextmanager
import json
import subprocess
from dataclasses import dataclass
from typing import Any, Iterator, Self


class JsonRPCTP:
    """JSON-RPC interface relied on by the jsonrpc-tp OCaml package."""

    @dataclass
    class Err[E]:
        """JSON-RPC error response, with a message and payload."""
        message: str
        data: E

    @dataclass
    class Resp[R]:
        """JSON-RPC response, with a payload."""
        result: R

    class Error(Exception):
        """Exception raised in case of protocol error."""
        pass

    def __init__(
            self,
            args: list[str],
            cwd: str | None = None,
            env: dict[str, str] | None = None
    ) -> None:
        self._process: subprocess.Popen | None = None
        self._counter: int = -1

        try:
            self._process = subprocess.Popen(
                args, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                cwd=cwd, env=env,
            )
        except Exception as e:
            self._process = None
            raise self.Error(f"Failed to start process: {e}") from e

    @contextmanager
    def sess(self) -> Iterator[Self]:
        """Context manager that calls quit upon __exit__."""
        yield self
        self.quit()

    def raw_request(
            self,
            method: str,
            params: list[Any],
    ) -> "JsonRPCTP.Resp[Any] | JsonRPCTP.Err[Any]":
        if self._process is None:
            raise self.Error("Not running anymore.")
        assert (self._process.stdin is not None)
        assert (self._process.stdout is not None)
        # Getting a fresh request id.
        self._counter = self._counter + 1
        fresh_id = self._counter
        # Preparing and sending the request.
        req = json.dumps({
            "jsonrpc": "2.0",
            "method": method,
            "params": params,
            "id": fresh_id
        }).encode()
        prefix = "Content-Length: "
        self._process.stdin.write(f"{prefix}{len(req) + 1}\r\n\r\n".encode())
        self._process.stdin.write(req)
        self._process.stdin.write(b"\n")
        self._process.stdin.flush()
        # Reading the response.
        header = self._process.stdout.readline().decode()
        _ = self._process.stdout.readline()
        try:
            nb_bytes = int(header[len(prefix):-2])
        except Exception as e:
            raise self.Error(f"Failed to parse response: {header}", e) from e
        response = self._process.stdout.read(nb_bytes).decode()
        response = json.loads(response)
        if "error" in response:
            error = response.get("error")
            return self.Err(error.get("message"), error.get("data"))
        else:
            return self.Resp(response.get("result"))

    def quit(self) -> None:
        if self._process is None:
            return
        _ = self.raw_request("quit", [])
        self._process.wait()
        self._process = None

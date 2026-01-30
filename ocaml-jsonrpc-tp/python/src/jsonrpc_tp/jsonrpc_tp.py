from __future__ import annotations  # noqa:I001

import json
import subprocess
from collections.abc import Iterator
from contextlib import contextmanager
from typing import (
    Any,
    Generic,
    Self,
    TypeVar,
    override,
)
from warnings import deprecated

T_co = TypeVar("T_co", covariant=True)


class JsonRPCTP:
    """JSON-RPC interface relied on by the jsonrpc-tp OCaml package."""

    # Note: custom because dataclass doesn't play nicely with
    # covariant data, cf. github.com/python/mypy/issues/17623
    #
    # Note: if we used pyright then we could use a simpler solution that still
    # uses dataclasses, cf. https://github.com/microsoft/pyright/discussions/11012
    class Reply(Generic[T_co]):
        """Base type of JsonRPC replies."""

        def __init__(self, data: T_co) -> None:
            self._data = data

        def __bool__(self) -> bool:
            raise NotImplementedError(
                f"implement in derivers of {self.__class__.__qualname__}"
            )

        def __eq__(self, other: Any) -> Any:
            if not issubclass(type(other), JsonRPCTP.Reply):
                return NotImplemented
            return (
                type(self) is type(other)
                and type(self._data) is type(other._data)
                and self._data == other._data
            )

        @override
        def __repr__(self) -> str:
            arg_reprs = ", ".join(
                [
                    f"data={repr(self.data)}",
                ]
            )
            return f"{self.__class__.__qualname__}({arg_reprs})"

        @property
        def data(self) -> T_co:
            return self._data

    # Note: custom because dataclass doesn't play nicely with
    # covariant data, cf. github.com/python/mypy/issues/17623
    #
    # Note: if we used pyright then we could use a simpler solution that still
    # uses dataclasses, cf. https://github.com/microsoft/pyright/discussions/11012
    class Err[T_co](Reply[T_co]):
        """JSON-RPC error response, with a message and optional payload."""

        def __init__(self, message: str, data: T_co) -> None:
            super().__init__(data=data)
            self._message = message

        @override
        def __repr__(self) -> str:
            arg_reprs = ", ".join(
                [
                    f"message={repr(self.message)}",
                    f"data={repr(self.data)}",
                ]
            )
            return f"{self.__class__.__qualname__}({arg_reprs})"

        @override
        def __bool__(self) -> bool:
            return False

        @override
        def __eq__(self, other: Any) -> Any:
            super_eq = super().__eq__(other)
            if super_eq is NotImplemented:
                return NotImplemented
            return super_eq and self.message == other.message

        @property
        def message(self) -> str:
            return self._message

        # Note: we inherit data property from Reply

    # Note: custom because dataclass doesn't play nicely with
    # covariant data, cf. github.com/python/mypy/issues/17623
    #
    # Note: if we used pyright then we could use a simpler solution that still
    # uses dataclasses, cf. https://github.com/microsoft/pyright/discussions/11012
    class Resp[T_co](Reply[T_co]):
        """Json-RPC response, with a payload."""

        def __init__(self, result: T_co) -> None:
            super().__init__(data=result)

        @override
        def __repr__(self) -> str:
            arg_reprs = ", ".join(
                [
                    f"result={repr(self.result)}",
                ]
            )
            return f"{self.__class__.__qualname__}({arg_reprs})"

        @override
        def __bool__(self) -> bool:
            return True

        # Note: while we inherit the data property from Reply, we
        # prefer to use the name result.
        @override
        @property
        @deprecated("Prefer Resp.result")
        def data(self) -> T_co:
            return super().data

        @property
        def result(self) -> T_co:
            return super().data

    class Error(Exception):
        """Exception raised in case of protocol error."""

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
            # Ignore the "ready" notification
            _ = self.recv()
        except Exception as e:
            self._process = None
            raise self.Error(f"Failed to start process: {e}") from e

    @contextmanager
    def sess(self) -> Iterator[Self]:
        """Context manager that calls quit upon __exit__."""
        yield self
        self.quit()

    def send(self, req):
        if self._process is None:
            raise self.Error("Not running anymore.")
        assert self._process.stdin is not None
        prefix = "Content-Length: "
        self._process.stdin.write(f"{prefix}{len(req) + 1}\r\n\r\n".encode())
        self._process.stdin.write(req)
        self._process.stdin.write(b"\n")
        self._process.stdin.flush()

    def recv(self):
        if self._process is None:
            raise self.Error("Not running anymore.")
        assert self._process.stdout is not None
        prefix = "Content-Length: "
        header: str = self._process.stdout.readline().decode()
        _ = self._process.stdout.readline()
        if not header.startswith(prefix):
            raise self.Error(f"Invalid message header: '{header}'")
        try:
            nb_bytes = int(header[len(prefix) : -2])
        except Exception as e:
            raise self.Error(f"Failed to parse header: {header}", e) from e
        response = self._process.stdout.read(nb_bytes).decode()
        return json.loads(response)

    def raw_request(
        self,
        method: str,
        params: list[Any],
    ) -> JsonRPCTP.Resp[Any] | JsonRPCTP.Err[Any]:
        # Getting a fresh request id.
        self._counter = self._counter + 1
        fresh_id = self._counter
        # Preparing and sending the request.
        req = json.dumps(
            {"jsonrpc": "2.0", "method": method, "params": params, "id": fresh_id}
        ).encode()
        self.send(req)
        # Reading the response.
        response = self.recv()
        if "error" in response:
            error = response.get("error")
            message = error.get("message")
            code = error.get("code")
            match code:
                # Request failed (taken from the LSP protocol)
                case -32803:
                    return self.Err(message, error.get("data"))
                # Method not found | Invalid params
                case -32601 | -32602:
                    raise Exception(message)
                # Anything else is unexpected.
                case _:
                    raise self.Error(f"Unexpected error code {code} ({message})")
        else:
            return self.Resp(response.get("result"))

    def quit(self) -> None:
        if self._process is None:
            return
        assert self._process.stdin is not None
        self._process.stdin.close()
        self._process.wait()
        self._process = None

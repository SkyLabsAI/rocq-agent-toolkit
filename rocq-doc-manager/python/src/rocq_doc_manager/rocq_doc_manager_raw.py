from dataclasses import dataclass
import json
import os
from pathlib import Path
import subprocess
from types import TracebackType
from typing import TypeVar, Generic, Any, List, Self

from rocq_doc_manager.dune_util import dune_env_hack

E = TypeVar('E')

@dataclass
class Err(Generic[E]):
    message: str
    data: E
    def ok(self) -> bool:
        return False

R = TypeVar('R')

@dataclass
class Resp(Generic[R]):
    result: R
    def ok(self) -> bool:
        return True

class RocqDocManagerRaw:
    class Error(Exception):
        pass

    def __init__(
            self,
            rocq_args: list[str],
            file_path: str,
            chdir: str | None = None,
            dune: bool = False,
            dune_disable_global_lock: bool = True,
    ) -> None:
        self._process: subprocess.Popen | None = None
        self._counter: int = -1

        try:
            env: dict[str, str] | None = None
            args: list[str] = []

            if dune:
                assert chdir is None

                # NOTE: workaround issue with [dune exec] not properly handling
                # the "--no-build" flag.
                if dune_disable_global_lock:
                    env = dune_env_hack()
                args = [
                    "dune", "exec", "--no-build", "--display=quiet",
                    "rocq-doc-manager", "--", file_path,
                    "--"
                ] + rocq_args
            else:
                args = ["rocq-doc-manager", file_path, "--"] + rocq_args
            self._process = subprocess.Popen(
                args, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                cwd=chdir, env=env,
            )
        except Exception as e:
            self._process = None
            raise self.Error(f"Failed to start process: {e}") from e

    # NOTE: a RocqDocManager instance can be used with a context manager;
    # __enter__ is a no-op, and __exit__ calls RocqDocManager.quit

    def __enter__(self) -> Self:
        return self

    def __exit__(
            self,
            exc_type: type[BaseException] | None,
            exc_value: BaseException | None,
            traceback: TracebackType | None,
    ) -> bool | None:
        self.quit()
        return None

    def request(self, method: str, params: List[Any]) -> Resp[Any] | Err[Any]:
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
            raise self.Error(f"Failed to parse response: {header}", e)
        response = self._process.stdout.read(nb_bytes).decode()
        response = json.loads(response)
        if "error" in response:
            error = response.get("error")
            return Err(error.get("message"), error.get("data"))
        else:
            return Resp(response.get("result"))

    def quit(self) -> None:
        if self._process is None:
            return
        _ = self.request("quit", [])
        self._process.wait()
        self._process = None

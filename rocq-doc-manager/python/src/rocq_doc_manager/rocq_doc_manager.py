from contextlib import contextmanager
import subprocess
import json
from dataclasses import dataclass
import threading
from types import TracebackType
from typing import Any, Iterator, Optional, List, Self


class RocqDocManager:
    # NOTES:
    # - class-variables, not instance variables
    # - a class-level lock is used to ensure that parallel calls to
    #   RocqDocManager.built_and_loaded will be sequenced
    _dune_build_lock: threading.Lock = threading.Lock()
    _process: Optional[subprocess.Popen] = None
    _counter: int = -1

    class Error(Exception):
        pass

    def __init__(
            self,
            rocq_args: list[str],
            file_path: str,
            chdir: str | None = None,
            dune: bool = False
    ) -> None:
        self._counter = -1
        try:
            args: list[str] = []
            if dune:
                # TODO: this pattern should probably be exposed separately
                dune_args = subprocess.run(["dune","coq","top","--no-build","--toplevel=rocq-fake-repl",file_path], capture_output=True)
                dune_args = dune_args.stdout.decode(encoding='utf-8')
                args = ["dune","exec","--no-build","rocq-doc-manager","--",file_path,"--"] + [x.strip() for x in dune_args.splitlines()]
                assert chdir is None
            else:
                args = ["rocq-doc-manager",file_path,"--"] + rocq_args
            self._process = subprocess.Popen(
                args, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                cwd=chdir
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

    # NOTE: important to use @contextmanager inside @classmethod
    @classmethod
    @contextmanager
    def built_and_loaded(
            cls,
            rocq_args: list[str],
            file_path: str,
            chdir: str | None = None,
            dune: bool = False,
    ) -> Iterator[Self]:
        """Context manager for working with built/loaded doc-mgrs; thread safe/blocking."""
        rdm = None
        # NOTE: [rdm.load_file()] seems to cause contention on the underlying
        # dune build lock. This might be due to how it invokes the sentence
        # splitter internally.
        with cls._dune_build_lock:
            rdm = cls(rocq_args, file_path, chdir=chdir, dune=dune)
            load_reply = rdm.load_file()
            if not isinstance(load_reply, RocqDocManager.Resp):
                raise IOError(f"Failed to load {file_path}: {load_reply}")
        try:
            yield rdm
        finally:
            if rdm is not None:
                rdm.quit()

    @dataclass
    class Err:
        message: str
        data: Any

    @dataclass
    class Resp:
        result: Any

    def request(self, method : str, params: List[Any]) -> Resp | Err:
        if self._process is None:
            raise self.Error("Not running anymore.")
        assert(self._process.stdin is not None)
        assert(self._process.stdout is not None)
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
        except:
            raise self.Error(f"Failed to parse response: {header}")
        response = self._process.stdout.read(nb_bytes).decode()
        response = json.loads(response)
        if "error" in response:
            error = response.get("error")
            return self.Err(error.get("message"), error.get("data"))
        else:
            return self.Resp(response.get("result"))

    def load_file(self):
        return self.request("load_file", [])

    def doc_prefix(self) -> List[Any]:
        result = self.request("doc_prefix", [])
        assert isinstance(result, self.Resp)
        return result.result

    def doc_suffix(self) -> List[Any]:
        result = self.request("doc_suffix", [])
        assert isinstance(result, self.Resp)
        return result.result

    def cursor_index(self) -> int:
        result = self.request("cursor_index", [])
        assert isinstance(result, self.Resp)
        assert isinstance(result.result, int)
        return result.result

    def run_step(self):
        return self.request("run_step", [])

    def run_command(self, cmd: str):
        return self.request("run_command", [cmd])

    def revert_before(self, erase: bool, index: int):
        return self.request("revert_before", [erase, index])

    def current_goal(self):
        result = self.run_command('idtac.')
        index = self.cursor_index()
        if isinstance(result, self.Err):
            _ = self.revert_before(True, index)
        return result

    def quit(self) -> None:
        if self._process is None:
            return
        _ = self.request("quit", [])
        self._process.wait()
        self._process = None

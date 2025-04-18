import subprocess
import json
from dataclasses import dataclass
from typing import Any
from typing import Optional
from typing import List

class RocqDocManager:
    _process : Optional[subprocess.Popen] = None
    _counter : int = -1

    class Error(Exception):
        pass

    def __init__(self, rocq_args, file_path) -> None:
        args = ["roc-doc-manager"] + rocq_args + [file_path]
        self._counter = -1
        try:
            self._process = subprocess.Popen(
              args, stdin=subprocess.PIPE, stdout=subprocess.PIPE
            )
        except Exception as e:
            self._process = None
            raise self.Error(f"Failed to start process: {e}") from e

    @dataclass
    class Err:
        message: str
        data: Any

    @dataclass
    class Resp:
        result: Any

    def request(self, method : str, params : List[Any]) -> Resp | Err:
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
        nb_bytes = int(header[len(prefix):-2])
        response = self._process.stdout.read(nb_bytes).decode()
        response = json.loads(response)
        if "error" in response:
            error = response.get("error")
            return self.Err(error.get("message"), error.get("data"))
        else:
            return self.Resp(response.get("result"))

    def quit(self) -> None:
        _ = self.request("quit", [])
        assert(self._process is not None)
        self._process.wait()
        self._process = None

def main():
    try:
        dm = RocqDocManager([], "test.v")
        print(dm.request("non-existant", []))
        print(dm.request("load_file", []))
        print(dm.request("doc_suffix", []))
        dm.quit()
    except RocqDocManager.Error as e:
        print(e)

if __name__ == '__main__':
    main()

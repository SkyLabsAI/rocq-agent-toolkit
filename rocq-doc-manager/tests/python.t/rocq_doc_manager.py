import subprocess
import json
from dataclasses import dataclass

class RocqDocManagerError(Exception):
    pass

@dataclass
class ErrorResponse:
    message: str
    data: any

@dataclass
class Response:
    result: any

class RocqDocManager:
    _process = None
    _counter = -1

    def __init__(self, rocq_args, file_path):
        args = ["rocq-doc-manager"] + rocq_args + [file_path]
        self._counter = -1
        try:
            self._process = subprocess.Popen(
              args, stdin=subprocess.PIPE, stdout=subprocess.PIPE
            )
        except Exception as e:
            self._process = None
            raise RocqDocManagerError(f"Failed to start process: {e}") from e

    def request(self, method, params):
        if self._process is None:
            raise RocqDocManagerError("Not running anymore.")
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
            return ErrorResponse(error.get("message"), error.get("data"))
        else:
            return Response(response.get("result"))

    def quit(self):
        _ = self.request("quit", [])
        self._process.wait()
        self._process = None

def main():
    dm = RocqDocManager([], "test.v")
    print(dm.request("non-existant", []))
    print(dm.request("load_file", []))
    print(dm.request("doc_suffix", []))
    dm.quit()

if __name__ == '__main__':
    main()

from __future__ import annotations  # noqa:I001

import asyncio
import json
from typing import (
    Self,
)

from .protocol import Backend
from .types import Error


class Process(Backend):
    _process: asyncio.subprocess.Process
    _running: bool
    _stdin: asyncio.streams.StreamWriter
    _stdout: asyncio.streams.StreamReader

    def __init__(self, process: asyncio.subprocess.Process) -> None:
        self._process = process
        self._running = True
        # https://github.com/python/typeshed/issues/13714
        assert self._process.stdin is not None
        assert self._process.stdout is not None
        self._stdin = self._process.stdin
        self._stdout = self._process.stdout

    @classmethod
    async def start(
        cls: type[Self],
        args: list[str],
        cwd: str | None = None,
        env: dict[str, str] | None = None,
    ) -> Self:
        inst: Self
        try:
            process = await asyncio.create_subprocess_exec(
                args[0],
                *args[1:],
                stdin=asyncio.subprocess.PIPE,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
                cwd=cwd,
                env=env,
            )
            inst = cls(process)
        except Exception as e:
            raise Error(f"Failed to start process: {e}") from e

        # Check the "ready_seq" notification
        try:
            ready = await inst.recv()
            ready = json.loads(ready)
            if "method" not in ready:
                raise Error(f"Unexpected packet: {ready} (not a notification)")
            method = ready.get("method")
            if method != "ready":
                raise Error(f'Got "{method}" notification instead of "ready"')
        except Exception as e:
            inst._process.kill()
            raise Error(f"Failed to start JSON-RPC service: {e}") from e
        return inst

    def check_running(self) -> None:
        if not self._running:
            raise Error("Process has been shut down.")

    async def send(self, payload: bytes):
        self.check_running()
        self._stdin.write(f"Content-Length: {len(payload) + 1}\r\n\r\n".encode())
        self._stdin.write(payload)
        self._stdin.write(b"\n")
        await self._stdin.drain()

    async def recv(self) -> bytes:
        self.check_running()
        prefix = "Content-Length: "
        try:
            raw_header: bytes = await self._stdout.readuntil()
        except asyncio.IncompleteReadError as e:
            if not self._running and e.partial == b"":
                raise asyncio.CancelledError() from e
            raise
        header: str = raw_header.decode()
        _ = await self._stdout.readuntil()
        if not header.startswith(prefix):
            self._process.kill()
            raise Error(f"Invalid message header: '{header}'")
        try:
            nb_bytes = int(header[len(prefix) : -2])
        except Exception as e:
            self._process.kill()
            raise Error(f"Failed to parse header: {header}", e) from e
        response: bytes = await self._stdout.readexactly(nb_bytes)
        return response

    async def quit(self) -> None:
        if not self._running:
            return
        self._stdin.close()
        # Wait for the process.
        await self._process.wait()
        self._running = False

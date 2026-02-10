from __future__ import annotations

import asyncio
from typing import Protocol


class BackendSync(Protocol):
    def send_sync(self, payload: bytes) -> None: ...

    def recv_sync(self) -> bytes: ...

    def quit_sync(self) -> None: ...


class Backend(BackendSync, Protocol):
    async def send(
        self,
        payload: bytes,
    ) -> None: ...

    async def recv(self) -> bytes: ...

    async def quit(self) -> None: ...

    # trivial sync wrappers
    def send_sync(self, payload: bytes) -> None:
        asyncio.run(self.send(payload))

    def recv_sync(self) -> bytes:
        return asyncio.run(self.recv())

    def quit_sync(self) -> None:
        return asyncio.run(self.quit())

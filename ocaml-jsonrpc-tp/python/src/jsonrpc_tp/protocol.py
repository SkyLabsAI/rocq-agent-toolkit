from __future__ import annotations

import asyncio
from typing import Protocol


class Backend(Protocol):
    async def send(
        self,
        payload: bytes,
    ) -> None: ...

    async def recv(self) -> bytes: ...

    # sync wrappers
    def send_sync(self, payload: bytes) -> None:
        asyncio.run(self.send(payload))

    def recv_sync(self) -> bytes:
        return asyncio.run(self.recv())

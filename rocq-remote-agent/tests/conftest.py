from __future__ import annotations

import pytest


class DummyWS:
    async def send(self, _message: str | bytes) -> None:  # pragma: no cover
        return None

    async def recv(self) -> str | bytes:  # pragma: no cover
        return b""

    async def close(self) -> None:  # pragma: no cover
        return None


@pytest.fixture
def dummy_ws() -> DummyWS:
    return DummyWS()

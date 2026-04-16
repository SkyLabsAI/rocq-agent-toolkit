"""Test helpers (ASGI apps without a real Rocq document manager)."""

from __future__ import annotations

import asyncio
from collections.abc import Callable
from pathlib import Path

from fastapi import FastAPI
from rocq_doc_manager import RocqCursor

from .main import session_router


def create_test_app(
    file_path: Path,
    cursor: RocqCursor,
    *,
    lock: asyncio.Lock | None = None,
    request_shutdown: Callable[[], None] | None = None,
) -> FastAPI:
    """FastAPI app with ``/feedback``, ``/health``, ``/quit``.

    Uses a caller-provided cursor (no lifespan). If ``request_shutdown`` is
    supplied, it will be called by ``POST /quit``; otherwise ``/quit`` returns
    503.
    """
    app = FastAPI()
    app.state.file_path = file_path
    app.state.cursor = cursor
    app.state.lock = lock if lock is not None else asyncio.Lock()
    if request_shutdown is not None:
        app.state.request_shutdown = request_shutdown
    app.include_router(session_router)
    return app

"""Test helpers (ASGI apps without a real Rocq document manager)."""

from __future__ import annotations

import asyncio
from pathlib import Path

from fastapi import FastAPI
from rocq_doc_manager import RocqCursor

from .main import session_router


def create_test_app(
    file_path: Path,
    cursor: RocqCursor,
    *,
    lock: asyncio.Lock | None = None,
) -> FastAPI:
    """FastAPI app with ``/feedback`` and ``/health``, using a provided cursor (no lifespan)."""
    app = FastAPI()
    app.state.file_path = file_path
    app.state.cursor = cursor
    app.state.lock = lock if lock is not None else asyncio.Lock()
    app.include_router(session_router)
    return app

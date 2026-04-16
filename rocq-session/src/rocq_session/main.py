"""FastAPI application for a single Rocq file session."""

from __future__ import annotations

import asyncio
from collections.abc import AsyncIterator
from contextlib import asynccontextmanager
from pathlib import Path

from fastapi import APIRouter, FastAPI, HTTPException, Query, Request
from rocq_doc_manager import create
from rocq_doc_manager import rocq_doc_manager_api as rdm_api

from .feedback import FeedbackPayload, feedback_at_byte
from .position import lsp_position_to_byte_offset

session_router = APIRouter(tags=["session"])


@session_router.get("/health")
async def health() -> dict[str, str]:
    return {"status": "ok"}


@session_router.get("/feedback")
async def feedback(
    request: Request,
    line: int = Query(ge=0, description="0-based line (LSP)"),
    character: int = Query(
        ge=0, description="0-based UTF-16 character offset on that line (LSP)"
    ),
) -> FeedbackPayload:
    file_path: Path = request.app.state.file_path
    try:
        source = file_path.read_text(encoding="utf-8")
    except UnicodeDecodeError as exc:
        raise HTTPException(
            status_code=400, detail="Source file is not valid UTF-8"
        ) from exc
    try:
        target_byte = lsp_position_to_byte_offset(source, line, character)
    except ValueError as exc:
        raise HTTPException(status_code=400, detail=str(exc)) from exc

    cursor = request.app.state.cursor
    lock = request.app.state.lock
    return await feedback_at_byte(cursor, target_byte, lock)


def create_app(
    file_path: Path,
    rocq_args: list[str],
    *,
    cwd: Path | None = None,
) -> FastAPI:
    """Build a FastAPI app bound to ``file_path`` (starts RDM in lifespan)."""
    resolved = file_path.resolve()

    @asynccontextmanager
    async def lifespan(app: FastAPI) -> AsyncIterator[None]:
        rdm = await create(str(resolved), rocq_args=rocq_args, cwd=cwd)
        load_reply = await rdm.load_file(0)
        if isinstance(load_reply, rdm_api.Err):
            msg = f"RocqDocManager.load_file failed: {load_reply.message}"
            raise RuntimeError(msg)
        app.state.cursor = rdm.cursor()
        app.state.lock = asyncio.Lock()
        app.state.rdm = rdm
        try:
            yield
        finally:
            await rdm.quit()

    app = FastAPI(title="rocq-session", lifespan=lifespan)
    app.state.file_path = resolved
    app.include_router(session_router)
    return app

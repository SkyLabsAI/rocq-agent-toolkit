"""Python API for the Rocq document manager.

This package provides a Python interface to interact with the Rocq document
manager.
"""

from collections.abc import AsyncIterator
from contextlib import asynccontextmanager
from pathlib import Path

from .rocq_cursor import RDMRocqCursor
from .rocq_cursor_protocol import RocqCursor
from .rocq_doc_manager import AsyncRocqDocManager, RocqDocManager


async def create(
    file_path: Path | str,
    *,
    rocq_args: list[str] | None = None,
    cwd: Path | str | None = None,
    dune: bool = False,
    dune_disable_global_lock: bool = True,
) -> AsyncRocqDocManager:
    """Build a RocqDocManager for the given file path.

    @param file_path will be interpreted as relative to the current working directory
      regardless of the value of `cwd`.
    """

    # TODO: It would be better to default to dune arguments
    return await AsyncRocqDocManager.create(
        [] if rocq_args is None else rocq_args,
        str(file_path),
        cwd=cwd,
        dune=dune,
        dune_disable_global_lock=dune_disable_global_lock,
    )


@asynccontextmanager
async def rdm_sess(
    file_path: Path | str,
    *,
    rocq_args: list[str] | None = None,
    cwd: Path | str | None = None,
    dune: bool = False,
    dune_disable_global_lock: bool = True,
    load_file: bool = True,
) -> AsyncIterator[AsyncRocqDocManager]:
    """Establish a session over a RocqDocManager on the given file.


    @param file_path will be interpreted as relative to the current working directory
      regardless of the value of `cwd`.
    """
    rdm = await create(
        file_path,
        rocq_args=rocq_args,
        cwd=cwd,
        dune=dune,
        dune_disable_global_lock=dune_disable_global_lock,
    )
    async with rdm.sess(load_file=load_file) as result:
        yield result


@asynccontextmanager
async def rc_sess(
    file_path: Path | str,
    *,
    rocq_args: list[str] | None = None,
    cwd: Path | str | None = None,
    dune: bool = False,
    dune_disable_global_lock: bool = True,
    load_file: bool = True,
) -> AsyncIterator[RocqCursor]:
    """Establish a session over a RocqCursor on the given file.

    @param file_path will be interpreted as relative to the current working directory
      regardless of the value of `cwd`.
    """
    async with rdm_sess(
        file_path,
        rocq_args=rocq_args,
        cwd=cwd,
        dune=dune,
        dune_disable_global_lock=dune_disable_global_lock,
        load_file=load_file,
    ) as rdm:
        yield rdm.cursor()


__all__ = [
    "create",
    "rdm_sess",
    "rc_sess",
    "RocqCursor",
    "RocqDocManager",
    "RDMRocqCursor",
]

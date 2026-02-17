"""Python API for the Rocq document manager.

This package provides a Python interface to interact with the Rocq document
manager.
"""

from .rocq_cursor import RDMRocqCursor
from .rocq_cursor_protocol import RocqCursor
from .rocq_doc_manager import AsyncRocqDocManager, RocqDocManager


def create(
    rocq_args: list[str],
    file_path: str,
    chdir: str | None = None,
    dune: bool = False,
    dune_disable_global_lock: bool = True,
) -> AsyncRocqDocManager:
    return AsyncRocqDocManager(
        rocq_args,
        file_path,
        chdir=chdir,
        dune=dune,
        dune_disable_global_lock=dune_disable_global_lock,
    )


__all__ = [
    "create",
    "RocqCursor",
    "RocqDocManager",
    "RDMRocqCursor",
]

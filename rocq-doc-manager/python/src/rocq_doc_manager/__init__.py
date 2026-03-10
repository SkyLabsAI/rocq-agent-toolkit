"""Python API for the Rocq document manager.

This package provides a Python interface to interact with the Rocq document
manager.
"""

from collections.abc import AsyncIterator
from contextlib import asynccontextmanager
from pathlib import Path
from typing import Literal

from rocq_dune_util import DuneError, in_dune_project, rocq_args_for

from .cursor.doc_cursor import RDMRocqCursor
from .cursor.protocol import RocqCursor
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
    rocq_args: Literal["dune", "auto"] | list[str] | None = None,
    cwd: Path | str | None = None,
    dune: bool = False,
    dune_disable_global_lock: bool = True,
    load_file: bool = True,
) -> AsyncIterator[RocqCursor]:
    """Establish a session over a RocqCursor on the given file.

    @param file_path will be interpreted as relative to the current working directory
      regardless of the value of `cwd`.
    """
    the_args: list[str] | None
    if isinstance(rocq_args, str):
        assert rocq_args in ["dune", "auto"]
        # The special case for when we want to get the default arguments
        # from dune
        try:
            the_args = rocq_args_for(file_path)
        except DuneError:
            # If a source root is detected, then raise
            # `err`. Otherwise use `[]`
            if rocq_args == "auto" and not in_dune_project(cwd=Path(file_path).parent):
                the_args = []
            else:
                raise
    else:
        the_args = rocq_args

    async with rdm_sess(
        file_path,
        rocq_args=the_args,
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

import logging
import re
from collections.abc import Iterator
from contextlib import contextmanager
from typing import Self, override

from jsonrpc_tp import JsonRPCTP

from rocq_doc_manager.rocq_cursor import RocqCursor

from .dune_util import dune_env_hack
from .rocq_doc_manager_api import RocqDocManagerAPI as API

logger = logging.getLogger(__name__)


class RocqDocManager(API):
    NO_GOAL_STRINGS: set[str] = {"No such goal.", "No more goals."}

    def __init__(
        self,
        rocq_args: list[str],
        file_path: str,
        chdir: str | None = None,
        dune: bool = False,
        dune_disable_global_lock: bool = True,
    ) -> None:
        env: dict[str, str] | None = None
        args: list[str] = []
        if dune:
            assert chdir is None

            # NOTE: workaround issue with [dune exec] not properly handling
            # the "--no-build" flag.
            if dune_disable_global_lock:
                env = dune_env_hack()
            args = [
                "dune",
                "exec",
                "--no-build",
                "--no-print-directory",
                "--display=quiet",
                "rocq-doc-manager",
                "--",
                file_path,
                "--",
            ] + rocq_args
        else:
            args = ["rocq-doc-manager", file_path, "--"] + rocq_args
        super().__init__(JsonRPCTP(args=args, cwd=chdir, env=env))
        self._file_path: str = file_path
        self._file_loaded: bool = False

    def __del__(self) -> None:
        if self._rpc:
            self._rpc.quit()

    def cursor(self) -> RocqCursor:
        return RocqCursor(self, 0)

    # ===== BEGIN: API patches ================================================
    # Note: patch load_file to raise/warn if the file is reloaded, since
    # this duplicates the document contents.
    @override
    def load_file(
        self,
        cursor: int,
        strict: bool = False,
    ) -> None | API.Err[API.RocqLoc | None]:
        if self._file_loaded:
            msg = f"reloading {self._file_path} duplicates document content"
            if strict:
                raise API.Error(msg)
            else:
                logger.warning(msg)
        return super().load_file(cursor)

    def quit(self) -> None:
        self._rpc.quit()

    # Note: patch insert_command since it is unsafe to
    # insert multiple commands without intervening blanks.
    @override
    def insert_command(
        self,
        cursor: int,
        text: str,
        blanks: str | None = "\n",
    ) -> API.CommandData | API.Err[API.CommandError | None]:
        insert_reply = super().insert_command(cursor, text)
        if isinstance(insert_reply, API.Err):
            return insert_reply
        if blanks is not None:
            if not re.match(r"\s+|\(\*.*\*\)", blanks):
                logger.warning(
                    " ".join(
                        [
                            "blanks should be whitespace or Rocq comments:",
                            f'"{blanks}"',
                        ]
                    )
                )
            self.insert_blanks(cursor, blanks)
        return insert_reply

    # ===== END: API patches ==================================================

    # ===== BEGIN: context managers ===========================================
    @contextmanager
    def sess(self, load_file: bool = True) -> Iterator[Self]:
        """A session will close the RDM after it completes"""
        with self._rpc.sess():
            if load_file:
                load_reply = self.load_file(0)
                if isinstance(load_reply, API.Err):
                    raise API.Error(f"RocqDocManager.load_file failed: {load_reply}")

            yield self
    # ===== END: context managers ==============================================

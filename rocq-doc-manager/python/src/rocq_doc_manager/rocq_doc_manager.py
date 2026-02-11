import logging
from collections.abc import Iterator
from contextlib import contextmanager
from pathlib import Path
from typing import Literal, Self, override

from jsonrpc_tp import JsonRPCTP
from rocq_dune_util import dune_env_hack, rocq_args_for

from . import rocq_doc_manager_api as rdm_api
from .plugin_registry import PluginRegistry
from .rocq_cursor import RocqCursor
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
        *,
        auto_discover_plugins: bool = True,
        plugin_names: list[str] | None = None,
    ) -> None:
        # Collect plugin dependencies if auto-discovery is enabled
        if auto_discover_plugins:
            extra_deps, workspace_deps = PluginRegistry.collect_plugin_deps(
                plugin_names=plugin_names
            )
            if extra_deps or workspace_deps:
                # Use rocq_args_for to get args with plugin dependencies
                # Convert workspace_deps to strings if needed
                workspace_deps_str = (
                    [str(d) for d in workspace_deps] if workspace_deps else None
                )
                rocq_args = rocq_args_for(
                    file_path,
                    cwd=chdir,
                    build=False,
                    extra_deps=extra_deps if extra_deps else None,
                    workspace_deps=workspace_deps_str,
                )

        env: dict[str, str] | None = None
        args: list[str] = []
        if dune:
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
        if hasattr(self, "_rpc") and self._rpc:
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
    ) -> None | rdm_api.Err[rdm_api.RocqLoc | None]:
        if self._file_loaded:
            msg = f"reloading {self._file_path} duplicates document content"
            if strict:
                raise rdm_api.Error(msg)
            else:
                logger.warning(msg)
        return super().load_file(cursor)

    def quit(self) -> None:
        self._rpc.quit()

    # Note: we used to patch the command here, but this introduces a circularity
    # between RocqDocManager and RocqCursor.
    # There are alternatives to this, e.g. to factor our the class reference,
    # but we ignore those for now.
    # @override
    # def insert_command(
    #     self, cursor: int, text: str, blanks: str | None = "\n", safe: bool = True
    # ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError | None]:
    #     if safe:
    #         prefix_reply = self.doc_prefix(cursor)
    #         if isinstance(prefix_reply, rdm_api.Err):
    #             # This is okay because the error is a cursor error
    #             return prefix_reply
    #         prefix: list[rdm_api.PrefixItem] = prefix_reply
    #         if prefix != [] and prefix[-1].kind != "blanks":
    #             self.insert_blanks(cursor, " ")
    #             revert = True
    #         else:
    #             revert = False
    #     else:
    #         revert = False

    #     try:
    #         result = super().insert_command(cursor, text)
    #         if isinstance(result, rdm_api.CommandError):
    #             if revert:
    #                 self.revert_before(cursor, erase=True, index=len(prefix))
    #         elif blanks is not None:
    #             self.insert_blanks(cursor, blanks)
    #         return result
    #     except rdm_api.Error:
    #         if revert:
    #             self.revert_before(cursor, erase=True, index=len(prefix))
    #         raise

    # ===== END: API patches ==================================================

    # ===== BEGIN: context managers ===========================================
    @contextmanager
    def sess(self, load_file: bool = True) -> Iterator[Self]:
        """A session will close the RDM after it completes"""
        if load_file:
            load_reply = self.load_file(0)
            if isinstance(load_reply, rdm_api.Err):
                raise rdm_api.Error(f"RocqDocManager.load_file failed: {load_reply}")
        yield self
        self.quit()

    # ===== END: context managers ==============================================
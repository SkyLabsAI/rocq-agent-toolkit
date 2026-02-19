from __future__ import annotations

from collections.abc import AsyncIterator, Iterator
from contextlib import asynccontextmanager, contextmanager
from typing import Self

from jsonrpc_tp import AsyncJsonRPCTP, JsonRPCTP
from jsonrpc_tp.jsonrpc_tp_async import AsyncProtocol
from rocq_dune_util import dune_env_hack

from . import rocq_doc_manager_api as rdm_api
from .rocq_cursor import RDMRocqCursor
from .rocq_cursor_protocol import RocqCursor
from .rocq_doc_manager_api import RocqDocManagerAPI as API
from .rocq_doc_manager_api import RocqDocManagerAPIAsync as AsyncAPI


def _rdm_command(
    *,
    dune: bool = False,
    dune_disable_global_lock: bool,
) -> tuple[dict[str, str] | None, list[str]]:
    if dune:
        # NOTE: workaround issue with [dune exec] not properly handling
        # the "--no-build" flag.
        env: dict[str, str] | None = None
        if dune_disable_global_lock:
            env = dune_env_hack()
        command = [
            "dune",
            "exec",
            "--no-build",
            "--no-print-directory",
            "--display=quiet",
            "rocq-doc-manager",
            "--",
        ]
        return (env, command)
    return (None, ["rocq-doc-manager"])


class RocqDocManager(API):
    def __init__(
        self,
        rocq_args: list[str],
        file_path: str,
        chdir: str | None = None,
        dune: bool = False,
        dune_disable_global_lock: bool = True,
    ) -> None:
        (env, command) = _rdm_command(
            dune=dune, dune_disable_global_lock=dune_disable_global_lock
        )
        args = command + [file_path, "--"] + rocq_args
        super().__init__(JsonRPCTP(args=args, cwd=chdir, env=env))

    # TODO: We can not implement this without a synchronous interface
    def cursor(self) -> RocqCursor:
        raise NotImplementedError("Synchronous cursor is not supported")
        # assert False
        # return RDMRocqCursor(self, 0)

    def quit(self) -> None:
        self._rpc.quit()

    @contextmanager
    def sess(self, load_file: bool = True) -> Iterator[Self]:
        """A session will close the RDM after it completes"""
        if load_file:
            load_reply = self.load_file(0)
            if isinstance(load_reply, rdm_api.Err):
                raise rdm_api.Error(
                    f"RocqDocManager.load_file failed: {load_reply.message}"
                )
        yield self
        self.quit()


class AsyncRocqDocManager(AsyncAPI):
    def __init__(self, rpc: AsyncProtocol) -> None:
        super().__init__(rpc)

    @staticmethod
    async def create(
        rocq_args: list[str],
        file_path: str,
        *,
        workers: int | None = None,
        chdir: str | None = None,
        dune: bool = False,
        dune_disable_global_lock: bool = True,
    ) -> AsyncRocqDocManager:
        (env, command) = _rdm_command(
            dune=dune, dune_disable_global_lock=dune_disable_global_lock
        )
        args = (
            command
            + ["--workers", str(1 if workers is None else workers), file_path, "--"]
            + rocq_args
        )
        rpc = AsyncJsonRPCTP(args=args, cwd=chdir, env=env)
        await rpc.start()
        return AsyncRocqDocManager(rpc)

    def cursor(self) -> RocqCursor:
        return RDMRocqCursor(self, 0)

    async def quit(self) -> None:
        await self._rpc.quit()

    @asynccontextmanager
    async def sess(self, load_file: bool = True) -> AsyncIterator[Self]:
        """A session will close the RDM after it completes"""
        if load_file:
            load_reply = await self.load_file(0)
            if isinstance(load_reply, rdm_api.Err):
                raise rdm_api.Error(
                    f"RocqDocManager.load_file failed: {load_reply.message}"
                )
        yield self
        await self.quit()

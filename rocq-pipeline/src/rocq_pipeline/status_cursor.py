"""A version of RocqCursor that prints the current proof script"""

from __future__ import annotations

import functools
from collections.abc import Awaitable, Callable, Coroutine

from rocq_doc_manager.rocq_cursor_protocol import DelegateRocqCursor, RocqCursor

from rocq_pipeline.agent.proof.trace import rdm_api


class WatchingCursor(DelegateRocqCursor):
    type CommandFinishCallback = Callable[[str, bool], None]

    def __init__(
        self,
        rc: RocqCursor,
        *,
        proof_script: Callable[[str], None],
        on_start_command: Callable[[str], None],
        on_finish_command: CommandFinishCallback,
        start: int = 0,
    ) -> None:
        super().__init__(rc)
        self._proof_script = proof_script
        self._on_start = on_start_command
        self._on_finish = on_finish_command
        self._start = start

    @staticmethod
    async def create(
        rc: RocqCursor,
        *,
        proof_script: Callable[[str], None],
        on_start_command: Callable[[str], None],
        on_finish_command: CommandFinishCallback,
    ) -> WatchingCursor:
        prefix = await rc.doc_prefix()
        return WatchingCursor(
            rc,
            proof_script=proof_script,
            on_start_command=on_start_command,
            on_finish_command=on_finish_command,
            start=len(prefix),
        )

    def make_derived(self, rc: RocqCursor) -> RocqCursor:
        return WatchingCursor(
            rc,
            proof_script=self._proof_script,
            start=self._start,
            on_start_command=self._on_start,
            on_finish_command=self._on_finish,
        )

    @staticmethod
    def updating_loc[**P, T](
        func: Callable[P, Awaitable[T]],
    ) -> Callable[P, Coroutine[None, None, T]]:
        @functools.wraps(func)
        async def wrapper(*args, **kwargs) -> T:
            self: WatchingCursor = args[0]
            result = await func(*args, **kwargs)
            prefix = await self.doc_prefix()
            script = "".join(x.text for x in prefix[self._start :] if x.kind != "ghost")
            self._proof_script(script)
            return result

        return wrapper

    @updating_loc
    async def _insert_command(
        self, text: str, *, ghost: bool = False
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        self._on_start(text)
        result = await super()._insert_command(text, ghost=ghost)
        self._on_finish(text, isinstance(result, rdm_api.CommandData))
        return result

    @updating_loc
    async def go_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        return await super().go_to(index)

    @updating_loc
    async def revert_before(self, erase: bool, index: int) -> None | rdm_api.Err[None]:
        return await super().revert_before(erase, index)

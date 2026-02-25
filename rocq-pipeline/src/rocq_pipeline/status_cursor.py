"""A version of RocqCursor that prints the current proof script"""

from __future__ import annotations

from collections.abc import Callable

from rocq_doc_manager.rocq_cursor_protocol import DelegateRocqCursor, RocqCursor
from wrapt.weakrefs import functools

from rocq_pipeline.agent.proof.trace import rdm_api


class WatchingCursor(DelegateRocqCursor):
    def __init__(
        self,
        rc: RocqCursor,
        *,
        proof_script: Callable[[str], None],
        start: int = 0,
    ) -> None:
        super().__init__(rc)
        self._proof_script = proof_script
        self._start = start

    @staticmethod
    async def create(
        rc: RocqCursor, *, proof_script: Callable[[str], None]
    ) -> WatchingCursor:
        prefix = await rc.doc_prefix()
        return WatchingCursor(rc, proof_script=proof_script, start=len(prefix))

    def make_derived(self, rc: RocqCursor) -> RocqCursor:
        return WatchingCursor(rc, proof_script=self._proof_script, start=self._start)

    @staticmethod
    def updating_loc[**P, T](func: Callable[P, T]) -> Callable[P, T]:
        @functools.wraps(func)
        async def wrapper(self: WatchingCursor, *args, **kwargs):
            result = await func(self, *args, **kwargs)
            prefix = await self.doc_prefix()
            script = "".join(x.text for x in prefix[self._start :] if x.kind != "ghost")
            self._proof_script(script)
            return result

        return wrapper

    @updating_loc
    async def _insert_command(
        self, text: str, *, ghost: bool = False
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        return await super()._insert_command(text, ghost=ghost)

    @updating_loc
    async def go_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        return await super().go_to(index)

    @updating_loc
    async def revert_before(self, erase: bool, index: int) -> None | rdm_api.Err[None]:
        return await super().revert_before(erase, index)

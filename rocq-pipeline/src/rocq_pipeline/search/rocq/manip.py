from __future__ import annotations

from typing import override

from rocq_doc_manager import RocqCursor

from ...search.search.search import StateManipulator


class RocqManipulator(StateManipulator[RocqCursor]):
    @override
    async def copy(self, state: RocqCursor) -> RocqCursor:
        return await state.clone()

    @override
    async def dispose(self, state: RocqCursor) -> None:
        await state.dispose()

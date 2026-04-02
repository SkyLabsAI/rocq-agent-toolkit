from __future__ import annotations

import logging
from typing import override

from .. import rocq_doc_manager_api as rdm_api
from .delegate import DelegateRocqCursor
from .delimited import DelimitedRocqCursor
from .protocol import RocqCursor

logger = logging.getLogger(__name__)


def list_endswith(ls: list, *, suffix: list) -> bool:
    return not suffix or ls[-len(suffix) :] == suffix


class GoalRocqCursor(DelegateRocqCursor):
    """
    A RocqCursor that can only work within a specific proof goal.
    """

    def __init__(
        self,
        cursor: RocqCursor,
        unfocused: list[int],
    ) -> None:
        super().__init__(cursor)
        self._unfocused = unfocused

    @classmethod
    async def make(
        cls,
        cursor: RocqCursor,
        *,
        start: int | None = None,
        end: int | None = None,
        count: int | None = None,
        materialize: bool = False,
    ) -> GoalRocqCursor | rdm_api.Err[rdm_api.CommandError | None]:
        """
        Creates a delimited cursor (as with `DelimitedRocqCursor.make`), with
        the added constraint that the cursor is not able to escape the current
        proof goal.

        @param cursor: see `DelimitedRocqCursor.make`
        @param start: see `DelimitedRocqCursor.make`
        @param end: see `DelimitedRocqCursor.make`
        @param count: see `DelimitedRocqCursor.make`
        @param materialize: see `DelimitedRocqCursor.make`
        @returns: the goal cursor or a command error
        @raises ValueError: see `DelimitedRocqCursor.make`
        @raises Exception: if the goal is created outside a proof or if there
            is not a single focused goal
        """
        # Create the underlying delimited cursor.
        delimited_cursor = await DelimitedRocqCursor.make(
            cursor, start=start, end=end, count=count, materialize=materialize
        )
        if isinstance(delimited_cursor, rdm_api.Err):
            return delimited_cursor
        # Check that we are in a proof.
        proof_state = await delimited_cursor.current_goal()
        if proof_state is None:
            raise Exception("Cannot create a goal cursor outside of a proof")
        # Check that there is a single focused goal.
        nb_focused = len(proof_state.focused_goals)
        if nb_focused != 1:
            raise Exception(
                f"Cannot create a goal cursor from {nb_focused} focused goals (expected 1)"
            )
        # Create the goal cursor.
        return cls(delimited_cursor, proof_state.unfocused_goals)

    def _escaped_goal(self, data: rdm_api.CommandData) -> bool:
        proof_state = data.proof_state
        if proof_state is None:
            return True
        return not list_endswith(proof_state.unfocused_goals, suffix=self._unfocused)

    async def closed(self) -> bool:
        proof_state = await self.current_goal()
        assert proof_state is not None
        prefix = (
            proof_state.unfocused_goals[: -len(self._unfocused)]
            if self._unfocused
            else proof_state.unfocused_goals
        )
        return all(n == 0 for n in prefix) and len(proof_state.focused_goals) == 0

    @override
    async def advance_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        raise NotImplementedError("advance_to")

    @override
    async def clone(self, *, materialize: bool = False) -> RocqCursor:
        cursor = await self._cursor.clone(materialize=materialize)
        return GoalRocqCursor(cursor, self._unfocused)

    @override
    async def go_to(
        self, index: int
    ) -> None | rdm_api.Err[rdm_api.CommandError | None]:
        raise NotImplementedError("go_to")

    @override
    async def _insert_command(
        self, text: str, *, ghost: bool = False
    ) -> rdm_api.CommandData | rdm_api.Err[rdm_api.CommandError]:
        revert = await self.cursor_index()
        data = await super()._insert_command(text, ghost=ghost)
        if isinstance(data, rdm_api.CommandData) and self._escaped_goal(data):
            await self.revert_before(erase=True, index=revert)
            raise Exception(f'Running command "{text}" would escape the goal')
        return data

    @override
    async def run_step(
        self,
    ) -> rdm_api.CommandData | None | rdm_api.Err[rdm_api.CommandError]:
        raise NotImplementedError("run_step")

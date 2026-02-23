from typing import override

import pytest
from pyroof_search import Action
from pyroof_search.rollout import Proposals, from_iterator
from pyroof_search.search import beam
from pyroof_search.strategy import Proposer


class MoveAction(Action[int]):
    def __init__(self, delta: int) -> None:
        self._delta = delta

    async def interact(self, state: int) -> int:
        return state + self._delta


class Around(Proposer[int, Action[int]]):
    @override
    async def rollout(
        self,
        state: int,
        max_rollout: int | None = None,
        context: Proposer.Context | None = None,
    ) -> Proposals[Action[int]]:
        return from_iterator(iter([(0.5, MoveAction(delta)) for delta in [1, -1]]))


@pytest.mark.asyncio
async def test_test_simple() -> None:
    search = beam.BeamSearch(Around(), max_depth=5)
    solutions = await search.search(0)
    assert len(solutions) == 0

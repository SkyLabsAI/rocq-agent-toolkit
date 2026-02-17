from typing import override

import pytest
from rocq_pipeline.search import Action
from rocq_pipeline.search.rollout import IteratorRollout, Rollout
from rocq_pipeline.search.search import beam
from rocq_pipeline.search.strategy import Strategy


class MoveAction(Action[int]):
    def __init__(self, delta: int) -> None:
        self._delta = delta

    async def interact(self, state: int) -> int:
        return state + self._delta


class Around(Strategy[int, Action[int]]):
    @override
    async def rollout(
        self,
        state: int,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action[int]]:
        return IteratorRollout(iter([(0.5, MoveAction(delta)) for delta in [1, -1]]))


@pytest.mark.asyncio
async def test_test_simple() -> None:
    search = beam.BeamSearch(Around(), max_depth=5)
    solutions = await search.search(0)
    assert len(solutions) == 0

"""Tests for rollout interleaving and repush behavior in search."""

from __future__ import annotations

from typing import override

import pytest
from rocq_pipeline.search.action import Action
from rocq_pipeline.search.search.frontier import BasicNode, Frontier
from rocq_pipeline.search.search.search import Node
from rocq_pipeline.search.strategy import MapStategy

from .util import FixedStrategy, OneShotFrontier, RecordingAction, run_search

pytestmark = pytest.mark.asyncio


class CountingStrategy(MapStategy[int, Action[int], int, Action[int]]):
    """Strategy that returns fixed rollouts per state and counts calls."""

    def __init__(self, mapping: dict[int, list[tuple[float, Action[int]]]]) -> None:
        self.call_counts: dict[int, int] = {}
        me = self

        def record(state: int) -> int:
            nonlocal me
            me.call_counts[state] = me.call_counts.get(state, 0) + 1
            return state

        super().__init__(
            FixedStrategy(mapping), into=record, outof=lambda _state, _state2, act: act
        )


class QueueFrontier[T](Frontier[T, BasicNode[T]]):
    """FIFO frontier that ignores child pushes to isolate repush behavior."""

    def __init__(self, candidates: list[T]) -> None:
        self._queue = [BasicNode(i, c) for i, c in enumerate(candidates)]
        self.repush_count = 0
        self._fresh = len(self._queue)

    def _next(self) -> int:
        self._fresh += 1
        return self._fresh

    @override
    def push(self, val: T, parent: BasicNode[T] | None) -> BasicNode[T]:
        return BasicNode(self._next(), val)

    @override
    def repush(self, node: BasicNode[T]) -> None:
        self.repush_count += 1
        self._queue.append(node)

    @override
    def clear(self) -> None:
        self._queue = []

    @override
    def take(self, count: int) -> list[tuple[T, BasicNode[T]]]:
        if not self._queue:
            return []
        pulled = self._queue[:count]
        self._queue = self._queue[count:]
        return [(x.state, x) for x in pulled]


async def test_explore_width_is_per_node_budget() -> None:
    """Verify explore_width limits actions per node per iteration."""
    record: list[str] = []
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        0: [
            (0.9, RecordingAction("c1_a1", record.append)),
            (0.85, RecordingAction("c1_a2", record.append)),
        ],
        1: [
            (0.8, RecordingAction("c2_a1", record.append)),
            (0.7, RecordingAction("c2_a2", record.append)),
        ],
    }
    strategy = FixedStrategy(actions)
    frontier = OneShotFrontier([Node(0, None), Node(1, None)])

    await run_search(strategy, frontier, beam_width=2, explore_width=2)

    assert record == ["c1_a1", "c1_a2", "c2_a1", "c2_a2"]


async def test_repush_and_rollout_reuse() -> None:
    """Verify repush happens when rollouts remain and rollouts are reused per node."""
    record: list[str] = []
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        0: [
            (0.9, RecordingAction("a1", record.append)),
            (0.8, RecordingAction("a2", record.append)),
        ]
    }
    strategy = CountingStrategy(actions)
    frontier = QueueFrontier([Node(0, None)])

    await run_search(strategy, frontier, beam_width=1, explore_width=1)

    assert record == ["a1", "a2"]
    assert frontier.repush_count == 2
    assert strategy.call_counts == {0: 1}


# This test does not make sense because asking for another solution is an operation
# that we need to "pay" for.
# def test_no_repush_when_rollout_exhausted() -> None:
#     """Ensure repush is not called once a rollout is exhausted."""
#     record: list[str] = []
#     actions: dict[int, list[tuple[float, Action[int]]]] = {
#         0: [(0.9, RecordingAction("only", record.append))]
#     }
#     strategy = CountingStrategy(actions)
#     frontier = QueueFrontier([Node(0, None)])

#     run_search(strategy, frontier, beam_width=1, explore_width=1)

#     assert record == ["only"]
#     assert frontier.repush_count == 0

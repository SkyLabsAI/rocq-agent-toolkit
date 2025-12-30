"""Tests for rollout interleaving and repush behavior in search."""

from __future__ import annotations

from typing import override

from rocq_pipeline.search.action import Action
from rocq_pipeline.search.search.frontier import Frontier
from rocq_pipeline.search.search.search import Node
from rocq_pipeline.search.strategy import Strategy

from .util import FixedStrategy, OneShotFrontier, RecordingAction, run_search


class CountingStrategy(Strategy[int]):
    """Strategy that returns fixed rollouts per state and counts calls."""

    def __init__(self, mapping: dict[int, list[tuple[float, Action[int]]]]) -> None:
        self._mapping = mapping
        self.call_counts: dict[int, int] = {}

    @override
    def rollout(
        self,
        state: int,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout[int]:
        self.call_counts[state] = self.call_counts.get(state, 0) + 1
        return iter(self._mapping.get(state, []))


class QueueFrontier[T](Frontier[T, T]):
    """FIFO frontier that ignores child pushes to isolate repush behavior."""

    def __init__(self, candidates: list[T]) -> None:
        self._queue = list(candidates)
        self.repush_count = 0

    @override
    def push(self, val: T, parent: T | None) -> None:
        return None

    @override
    def repush(self, node: T) -> None:
        self.repush_count += 1
        self._queue.append(node)

    @override
    def clear(self) -> None:
        self._queue = []

    @override
    def take(self, count: int) -> list[tuple[T, T]] | None:
        if not self._queue:
            return None
        pulled = self._queue[:count]
        self._queue = self._queue[count:]
        return [(node, node) for node in pulled]


def test_explore_width_is_global_budget() -> None:
    """Verify explore_width limits total actions across the beam per iteration."""
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

    frontier_base: Frontier[Node[int], Node[int]] = frontier
    run_search(strategy, frontier_base, beam_width=2, explore_width=2)

    assert record == ["c1_a1", "c1_a2"]


def test_repush_and_rollout_reuse() -> None:
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

    frontier_base: Frontier[Node[int], Node[int]] = frontier
    run_search(strategy, frontier_base, beam_width=1, explore_width=1)

    assert record == ["a1", "a2"]
    assert frontier.repush_count == 1
    assert strategy.call_counts == {0: 1}


def test_no_repush_when_rollout_exhausted() -> None:
    """Ensure repush is not called once a rollout is exhausted."""
    record: list[str] = []
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        0: [(0.9, RecordingAction("only", record.append))]
    }
    strategy = CountingStrategy(actions)
    frontier = QueueFrontier([Node(0, None)])

    frontier_base: Frontier[Node[int], Node[int]] = frontier
    run_search(strategy, frontier_base, beam_width=1, explore_width=1)

    assert record == ["only"]
    assert frontier.repush_count == 0

"""Tests for max_depth gating in search."""

from __future__ import annotations

from typing import override

from rocq_pipeline.search.action import Action
from rocq_pipeline.search.search.frontier import Frontier
from rocq_pipeline.search.search.search import (
    Node,
    RepetitionPolicy,
    Search,
    StateManipulator,
)
from rocq_pipeline.search.strategy import Strategy


class RecordingAction(Action[int]):
    """Action that records successful execution."""

    def __init__(self, key: str, record: list[str]) -> None:
        self._key = key
        self._record = record

    @override
    def interact(self, state: int) -> int:
        self._record.append(self._key)
        return state

    def key(self) -> str:
        return self._key


class FixedStrategy(Strategy[int]):
    """Strategy that returns fixed rollouts per state."""

    def __init__(self, mapping: dict[int, list[tuple[float, Action[int]]]]) -> None:
        self._mapping = mapping

    @override
    def rollout(
        self,
        state: int,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout[int]:
        return iter(self._mapping.get(state, []))


class QueueFrontier(Frontier[Node[int], Node[int]]):
    """Simple FIFO frontier for max_depth tests."""

    def __init__(self, candidates: list[Node[int]]) -> None:
        self._queue = list(candidates)

    @override
    def push(self, val: Node[int], parent: Node[int] | None) -> None:
        self._queue.append(val)

    @override
    def repush(self, node: Node[int]) -> None:
        self._queue.append(node)

    @override
    def clear(self) -> None:
        self._queue = []

    @override
    def take(self, count: int) -> list[tuple[Node[int], Node[int]]] | None:
        if not self._queue:
            return None
        pulled = self._queue[:count]
        self._queue = self._queue[count:]
        return [(node, node) for node in pulled]


def run_search(
    strategy: Strategy[int],
    worklist: Frontier[Node[int], Node[int]],
    beam_width: int = 1,
    explore_width: int = 1,
    repetition_policy: RepetitionPolicy | None = None,
    state_manip: StateManipulator[int] | None = None,
    max_depth: int | None = None,
) -> Frontier[Node[int], Node[int]]:
    """Call continue_search with a concrete Frontier instance (mypy helper)."""
    return Search.continue_search(
        strategy,
        worklist,
        beam_width=beam_width,
        explore_width=explore_width,
        repetition_policy=repetition_policy,
        state_manip=state_manip,
        max_depth=max_depth,
    )  # type: ignore[type-var]


def test_max_depth_blocks_deeper_nodes() -> None:
    """Ensure nodes deeper than max_depth are skipped while depth==max_depth proceeds."""
    record: list[str] = []
    root = Node(0, None)
    depth_one = Node(1, root, action_key="d1")
    depth_two = Node(2, depth_one, action_key="d2")
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        depth_one.state: [(0.9, RecordingAction("d1", record))],
        depth_two.state: [(0.8, RecordingAction("d2", record))],
    }
    strategy = FixedStrategy(actions)
    frontier = QueueFrontier([depth_one, depth_two])

    frontier_base: Frontier[Node[int], Node[int]] = frontier
    run_search(
        strategy,
        frontier_base,
        beam_width=2,
        explore_width=2,
        max_depth=1,
    )

    assert record == ["d1"]

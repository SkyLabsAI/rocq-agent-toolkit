"""Tests for StateManipulator hooks in search."""

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


class CountingStateManipulator(StateManipulator[int]):
    """State manipulator that counts copy and dispose calls."""

    def __init__(self) -> None:
        self.copy_count: int = 0
        self.dispose_count: int = 0

    def copy(self, state: int) -> int:
        self.copy_count += 1
        return state

    def dispose(self, state: int) -> None:
        self.dispose_count += 1


class RecordingAction(Action[int]):
    """Action that records successful execution."""

    def __init__(self, key: str, record: list[str], advance_by: int = 0) -> None:
        self._key = key
        self._record = record
        self._advance_by = advance_by

    @override
    def interact(self, state: int) -> int:
        self._record.append(self._key)
        return state + self._advance_by

    def key(self) -> str:
        return self._key


class FailingAction(Action[int]):
    """Action that always fails."""

    def __init__(self, key: str) -> None:
        self._key = key

    @override
    def interact(self, state: int) -> int:
        raise Action.Failed()

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
    """Simple FIFO frontier for state manipulator tests."""

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


def make_chain(keys: list[str]) -> Node[int]:
    """Build a node chain where each key becomes the action_key on the next node."""
    parent: Node[int] | None = None
    state = 0
    for key in keys:
        parent = Node(state, parent, action_key=key)
        state += 1
    assert parent is not None
    return parent


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


def test_copy_called_on_success() -> None:
    """Ensure copy() is called for successful action attempts."""
    record: list[str] = []
    manip = CountingStateManipulator()
    candidate = Node(0, None)
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        0: [(0.9, RecordingAction("ok", record, advance_by=1))]
    }
    strategy = FixedStrategy(actions)
    frontier = QueueFrontier([candidate])

    frontier_base: Frontier[Node[int], Node[int]] = frontier
    run_search(strategy, frontier_base, state_manip=manip)

    assert manip.copy_count == 1
    assert manip.dispose_count == 0
    assert record == ["ok"]


def test_dispose_called_on_failure() -> None:
    """Ensure dispose() is called when an action fails."""
    manip = CountingStateManipulator()
    candidate = Node(0, None)
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        0: [(0.9, FailingAction("fail"))]
    }
    strategy = FixedStrategy(actions)
    frontier = QueueFrontier([candidate])

    frontier_base: Frontier[Node[int], Node[int]] = frontier
    run_search(strategy, frontier_base, state_manip=manip)

    assert manip.copy_count == 1
    assert manip.dispose_count == 1


def test_copy_not_called_on_dedup_skip() -> None:
    """Ensure copy() is not called when a duplicate action is skipped."""
    manip = CountingStateManipulator()
    record: list[str] = []
    candidate = Node(0, None)
    candidate.remember_action("dup")
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        0: [(0.9, RecordingAction("dup", record))]
    }
    strategy = FixedStrategy(actions)
    frontier = QueueFrontier([candidate])

    frontier_base: Frontier[Node[int], Node[int]] = frontier
    run_search(strategy, frontier_base, state_manip=manip)

    assert manip.copy_count == 0
    assert record == []


def test_copy_not_called_on_repetition_skip() -> None:
    """Ensure copy() is not called when repetition policy skips an action."""
    manip = CountingStateManipulator()
    record: list[str] = []
    candidate = make_chain(["x", "x"])
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        candidate.state: [(0.9, RecordingAction("x", record))]
    }
    strategy = FixedStrategy(actions)
    policy = RepetitionPolicy(
        max_consecutive=2, min_pattern_len=2, max_pattern_len=2, min_reps=2
    )
    frontier = QueueFrontier([candidate])

    frontier_base: Frontier[Node[int], Node[int]] = frontier
    run_search(
        strategy,
        frontier_base,
        repetition_policy=policy,
        state_manip=manip,
    )

    assert manip.copy_count == 0
    assert record == []


def test_copy_not_called_on_max_depth_skip() -> None:
    """Ensure copy() is not called when max_depth skips an action."""
    manip = CountingStateManipulator()
    record: list[str] = []
    parent = Node(0, None)
    candidate = Node(1, parent, action_key="d2")
    candidate = Node(2, candidate, action_key="d3")
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        candidate.state: [(0.9, RecordingAction("deep", record))]
    }
    strategy = FixedStrategy(actions)
    frontier = QueueFrontier([candidate])

    frontier_base: Frontier[Node[int], Node[int]] = frontier
    run_search(
        strategy,
        frontier_base,
        max_depth=1,
        state_manip=manip,
    )

    assert manip.copy_count == 0
    assert record == []

"""Tests for repetition detection and gating in search."""

from __future__ import annotations

from typing import override

from rocq_pipeline.search.action import Action
from rocq_pipeline.search.search.frontier import Frontier
from rocq_pipeline.search.search.search import (
    Node,
    RepetitionPolicy,
    Search,
    StateManipulator,
    _has_action_repetition,
)
from rocq_pipeline.search.strategy import Strategy


class RecordingAction(Action[int]):
    """Action that records when it is executed."""

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
    """Simple FIFO frontier for repetition tests."""

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


def test_has_action_repetition_consecutive() -> None:
    """Ensure consecutive repetition is detected."""
    policy = RepetitionPolicy(
        max_consecutive=2, min_pattern_len=2, max_pattern_len=3, min_reps=2
    )
    hit, reason = _has_action_repetition(["x", "x", "x"], policy)
    assert hit is True
    assert reason == "consecutive_2"


def test_has_action_repetition_cyclic() -> None:
    """Ensure cyclic repetition is detected."""
    policy = RepetitionPolicy(
        max_consecutive=3, min_pattern_len=2, max_pattern_len=2, min_reps=2
    )
    hit, reason = _has_action_repetition(["a", "b", "a", "b"], policy)
    assert hit is True
    assert reason == "cyclic_len2"


def test_repetition_policy_skips_repeated_action() -> None:
    """Ensure repetition policy skips actions that repeat recent history."""
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
        beam_width=1,
        explore_width=1,
        repetition_policy=policy,
    )

    assert record == []


def test_repetition_policy_uses_bounded_history() -> None:
    """Ensure repetition checks ignore action history outside the bounded tail."""
    record: list[str] = []
    candidate = make_chain(["a", "a", "a", "b", "c"])
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        candidate.state: [(0.9, RecordingAction("a", record, advance_by=1))]
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
        beam_width=1,
        explore_width=1,
        repetition_policy=policy,
    )

    assert record == ["a"]

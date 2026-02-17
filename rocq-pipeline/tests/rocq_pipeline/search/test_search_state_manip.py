"""Tests for StateManipulator hooks in search."""

from __future__ import annotations

from typing import override

import pytest
from rocq_pipeline.search.action import Action
from rocq_pipeline.search.search.search import Node, RepetitionPolicy, StateManipulator

from .util import (
    FixedStrategy,
    RecordingAction,
    make_chain,
    run_search,
    seeded_bfs,
)


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


class FailingAction(Action[int]):
    """Action that always fails."""

    def __init__(self, key: str) -> None:
        self._key = key

    @override
    async def interact(self, state: int) -> int:
        raise Action.Failed()

    def key(self) -> str:
        return self._key


@pytest.mark.asyncio
async def test_copy_called_on_success() -> None:
    """Ensure copy() is called for successful action attempts."""
    record: list[str] = []
    manip = CountingStateManipulator()
    candidate = Node(0, None)
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        0: [(0.9, RecordingAction("ok", record.append, advance_by=1))]
    }
    strategy = FixedStrategy(actions)
    frontier = seeded_bfs([candidate])
    await run_search(strategy, frontier, state_manip=manip)

    assert manip.copy_count == 1
    assert manip.dispose_count == 0
    assert record == ["ok"]


@pytest.mark.asyncio
async def test_dispose_called_on_failure() -> None:
    """Ensure dispose() is called when an action fails."""
    manip = CountingStateManipulator()
    candidate = Node(0, None)
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        0: [(0.9, FailingAction("fail"))]
    }
    strategy = FixedStrategy(actions)
    frontier = seeded_bfs([candidate])
    await run_search(strategy, frontier, state_manip=manip)

    assert manip.copy_count == 1
    assert manip.dispose_count == 1


@pytest.mark.asyncio
async def test_copy_not_called_on_dedup_skip() -> None:
    """Ensure copy() is not called when a duplicate action is skipped."""
    manip = CountingStateManipulator()
    record: list[str] = []
    candidate = Node(0, None)
    candidate.remember_action("dup")
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        0: [(0.9, RecordingAction("dup", record.append))]
    }
    strategy = FixedStrategy(actions)
    frontier = seeded_bfs([candidate])
    await run_search(strategy, frontier, state_manip=manip)

    assert manip.copy_count == 0
    assert record == []


@pytest.mark.asyncio
async def test_copy_not_called_on_repetition_skip() -> None:
    """Ensure copy() is not called when repetition policy skips an action."""
    manip = CountingStateManipulator()
    record: list[str] = []
    candidate = make_chain(["x", "x"])
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        candidate.state: [(0.9, RecordingAction("x", record.append))]
    }
    strategy = FixedStrategy(actions)
    policy = RepetitionPolicy(
        max_consecutive=2, min_pattern_len=2, max_pattern_len=2, min_reps=2
    )
    frontier = seeded_bfs([candidate])
    await run_search(strategy, frontier, repetition_policy=policy, state_manip=manip)

    assert manip.copy_count == 0
    assert record == []


@pytest.mark.asyncio
async def test_copy_not_called_on_max_depth_skip() -> None:
    """Ensure copy() is not called when max_depth skips an action."""
    manip = CountingStateManipulator()
    record: list[str] = []
    parent = Node(0, None)
    candidate = Node(1, parent, action_key="d2")
    candidate = Node(2, candidate, action_key="d3")
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        candidate.state: [(0.9, RecordingAction("deep", record.append))]
    }
    strategy = FixedStrategy(actions)
    frontier = seeded_bfs([candidate])
    await run_search(strategy, frontier, max_depth=1, state_manip=manip)

    assert manip.copy_count == 0
    assert record == []

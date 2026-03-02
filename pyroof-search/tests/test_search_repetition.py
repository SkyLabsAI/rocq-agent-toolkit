"""Tests for repetition detection and gating in search."""

from __future__ import annotations

import pytest
from pyroof_search.action import Action
from pyroof_search.search.search import (
    RepetitionPolicy,
    _has_action_repetition,
)

from .util import (
    FixedStrategy,
    RecordingAction,
    make_chain,
    run_search,
    seeded_bfs,
)


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


@pytest.mark.asyncio
async def test_repetition_policy_skips_repeated_action() -> None:
    """Ensure repetition policy skips actions that repeat recent history."""
    record: list[str] = []
    candidate = make_chain(["x", "x"])
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        candidate.state: [(0.9, RecordingAction("x", record.append))]
    }
    strategy = FixedStrategy(actions)
    policy = RepetitionPolicy(
        max_consecutive=2, min_pattern_len=2, max_pattern_len=2, min_reps=2
    )
    frontier = await seeded_bfs([candidate])
    await run_search(
        strategy, frontier, beam_width=1, explore_width=1, repetition_policy=policy
    )

    assert record == []


@pytest.mark.asyncio
async def test_repetition_policy_uses_bounded_history() -> None:
    """Ensure repetition checks ignore action history outside the bounded tail."""
    record: list[str] = []
    candidate = make_chain(["a", "a", "a", "b", "c"])
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        candidate.state: [(0.9, RecordingAction("a", record.append, advance_by=1))]
    }
    strategy = FixedStrategy(actions)
    policy = RepetitionPolicy(
        max_consecutive=2, min_pattern_len=2, max_pattern_len=2, min_reps=2
    )
    frontier = await seeded_bfs([candidate])
    await run_search(
        strategy, frontier, beam_width=1, explore_width=1, repetition_policy=policy
    )

    assert record == ["a"]

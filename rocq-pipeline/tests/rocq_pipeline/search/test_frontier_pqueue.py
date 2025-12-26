"""Tests for the PQueue frontier."""

from __future__ import annotations

import pytest
from rocq_pipeline.search.search.frontier import PQueue


def _numeric_compare(a: int, b: int) -> int:
    """Three-way comparator for priority queue ordering."""
    return (a > b) - (a < b)


def test_pqueue_priority_ordering(push_values: list[int]) -> None:
    """Verify PQueue returns states ordered by score. Lower scores should come out first for the comparator."""
    frontier: PQueue[int] = PQueue(score=lambda v: v, compare=_numeric_compare)
    for value in push_values:
        frontier.push(value, None)
    taken = frontier.take(len(push_values))
    assert taken is not None
    states = [state for state, _ in taken]
    assert states == sorted(push_values)


def test_pqueue_tiebreaks_by_id() -> None:
    """Verify PQueue ties break by insertion id. This keeps ordering deterministic when scores match."""
    frontier: PQueue[str] = PQueue(score=lambda _: 0, compare=_numeric_compare)
    frontier.push("first", None)
    frontier.push("second", None)
    taken = frontier.take(2)
    assert taken is not None
    states = [state for state, _ in taken]
    assert states == ["first", "second"]


def test_pqueue_respects_count(push_values: list[int], take_count: int) -> None:
    """Ensure PQueue take respects count limits. The frontier should not drain more than requested."""
    if take_count <= 0 or take_count >= len(push_values):
        pytest.skip("Need 0 < take_count < len(push_values) to test count handling.")
    frontier: PQueue[int] = PQueue(score=lambda v: v, compare=_numeric_compare)
    for value in push_values:
        frontier.push(value, None)
    taken = frontier.take(take_count)
    assert taken is not None
    assert len(taken) == take_count

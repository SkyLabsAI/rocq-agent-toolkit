"""Baseline interface tests for frontier implementations."""

from __future__ import annotations

from rocq_pipeline.search.search.frontier import BFS, DFS


def test_take_empty_returns_none() -> None:
    """Ensure empty frontiers return None on take. This matches the search loop termination contract."""
    assert DFS[int]().take(1) is None
    assert BFS[int]().take(1) is None

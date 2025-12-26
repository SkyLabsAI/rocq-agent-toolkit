"""Tests for the RememberTrace frontier wrapper."""

from __future__ import annotations

from rocq_pipeline.search.search.frontier import BFS, BasicNode, RememberTrace


def test_remember_trace_push_and_repush() -> None:
    """Verify RememberTrace records push and repush entries. Repush entries should be tagged with None values."""
    base = BFS[int]()
    frontier = RememberTrace(
        base,
        is_solution=lambda _: False,
        stop_on_first_solution=False,
    )
    parent = BasicNode(1, 99)
    frontier.push(1, parent)
    node = BasicNode(2, 2)
    frontier.repush(node)
    assert frontier.visited_nodes() == [(1, parent), (None, node)]


def test_remember_trace_clear_resets() -> None:
    """Ensure RememberTrace clear resets the trace history. A fresh run should not include prior visits."""
    base = BFS[int]()
    frontier = RememberTrace(
        base,
        is_solution=lambda _: False,
        stop_on_first_solution=False,
    )
    frontier.push(1, None)
    frontier.clear()
    assert frontier.visited_nodes() == []

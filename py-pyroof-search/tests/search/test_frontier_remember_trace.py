"""Tests for the RememberTrace frontier wrapper."""

from __future__ import annotations

import pytest
from rocq_pipeline.search.search.frontier import BFS, BasicNode, RememberTrace


async def is_solution_False(_) -> bool:
    return False


@pytest.mark.asyncio
async def test_remember_trace_push_and_repush() -> None:
    """Verify RememberTrace records push and repush entries. Repush entries should be tagged with None values."""
    base = BFS[int]()
    frontier = RememberTrace(
        base,
        is_solution=is_solution_False,
        stop_on_first_solution=False,
    )
    parent = BasicNode(1, 99)
    await frontier.push(1, parent)
    node = BasicNode(2, 2)
    await frontier.repush(node)
    assert frontier.visited_nodes() == [(1, parent), (None, node)]


@pytest.mark.asyncio
async def test_remember_trace_clear_resets() -> None:
    """Ensure RememberTrace clear resets the trace history. A fresh run should not include prior visits."""
    base = BFS[int]()
    frontier = RememberTrace(
        base,
        is_solution=is_solution_False,
        stop_on_first_solution=False,
    )
    await frontier.push(1, None)
    await frontier.clear()
    assert frontier.visited_nodes() == []

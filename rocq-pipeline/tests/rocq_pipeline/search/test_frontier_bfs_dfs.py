"""Tests for BFS and DFS frontiers."""

from __future__ import annotations

import pytest
from rocq_pipeline.search.search.frontier import BFS, DFS


def test_dfs_ordering(push_values: list[int], take_count: int) -> None:
    """Verify DFS returns values in LIFO order. This checks stack behavior for depth-first search."""
    if take_count <= 0:
        pytest.skip("take_count must be positive for ordering checks.")
    assert len(push_values) >= 2
    frontier = DFS[int]()
    for value in push_values:
        frontier.push(value, None)
    taken = frontier.take(take_count)
    assert taken is not None
    states = [state for state, _ in taken]
    assert states == list(reversed(push_values))[:take_count]


def test_bfs_ordering(push_values: list[int], take_count: int) -> None:
    """Verify BFS returns values in FIFO order. This checks queue behavior for breadth-first search."""
    if take_count <= 0:
        pytest.skip("take_count must be positive for ordering checks.")
    assert len(push_values) >= 2
    frontier = BFS[int]()
    for value in push_values:
        frontier.push(value, None)
    taken = frontier.take(take_count)
    assert taken is not None
    states = [state for state, _ in taken]
    assert states == push_values[:take_count]


def test_dfs_repush_front(push_values: list[int]) -> None:
    """Ensure DFS repush restores the node to the front. This preserves LIFO expansion after partial pulls."""
    assert len(push_values) >= 2
    frontier = DFS[int]()
    for value in push_values:
        frontier.push(value, None)
    taken = frontier.take(1)
    assert taken is not None
    state, node = taken[0]
    frontier.repush(node)
    next_take = frontier.take(1)
    assert next_take is not None
    assert next_take[0][0] == state


def test_bfs_repush_appends(push_values: list[int]) -> None:
    """Ensure BFS repush appends the node to the back. This preserves FIFO expansion after partial pulls."""
    assert len(push_values) >= 2
    frontier = BFS[int]()
    for value in push_values:
        frontier.push(value, None)
    first = frontier.take(1)
    assert first is not None
    state, node = first[0]
    frontier.repush(node)
    rest = frontier.take(len(push_values))
    assert rest is not None
    states = [value for value, _ in rest]
    assert states == push_values[1:] + [state]

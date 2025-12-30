"""Core tests for search termination and setup behavior."""

from __future__ import annotations

from collections.abc import Callable
from typing import override

import pytest
from rocq_pipeline.search.search.frontier import Frontier
from rocq_pipeline.search.search.search import Node, Search
from rocq_pipeline.search.strategy import FailStrategy, Strategy

from .util import run_search


class StaticFrontier(Frontier[Node[int], Node[int]]):
    """Frontier that returns a fixed sequence of take results."""

    def __init__(
        self, take_returns: list[list[tuple[Node[int], Node[int]]] | None]
    ) -> None:
        self._take_returns = list(take_returns)
        self.take_calls: list[int] = []
        self.pushed: list[Node[int]] = []

    @override
    def push(self, val: Node[int], parent: Node[int] | None) -> None:
        self.pushed.append(val)

    @override
    def repush(self, node: Node[int]) -> None:
        return None

    @override
    def clear(self) -> None:
        return None

    @override
    def take(self, count: int) -> list[tuple[Node[int], Node[int]]] | None:
        self.take_calls.append(count)
        if not self._take_returns:
            return None
        return self._take_returns.pop(0)


def run_search_with_factory(
    strategy: Strategy[int],
    start: int,
    frontier: Callable[[], Frontier[Node[int], Node[int]]],
) -> Frontier[Node[int], Node[int]]:
    """Call search with a frontier factory (mypy helper)."""
    return Search.search(strategy, start, frontier=frontier)  # type: ignore[type-var]


def test_search_returns_frontier_instance() -> None:
    """Verify Search.search calls the frontier factory once and returns that instance."""
    frontier = StaticFrontier([None])
    calls = 0

    def make_frontier() -> Frontier[Node[int], Node[int]]:
        nonlocal calls
        calls += 1
        return frontier

    result = run_search_with_factory(FailStrategy(), 0, make_frontier)
    assert result is frontier
    assert calls == 1
    assert len(frontier.pushed) == 1


def test_continue_search_terminates_on_none() -> None:
    """Ensure continue_search returns when take() yields None."""
    frontier = StaticFrontier([None])
    frontier_base: Frontier[Node[int], Node[int]] = frontier
    result = run_search(FailStrategy(), frontier_base, beam_width=2)
    assert result is frontier
    assert frontier.take_calls == [2]


def test_continue_search_terminates_on_empty_list() -> None:
    """Ensure continue_search returns when take() yields an empty list."""
    frontier = StaticFrontier([[]])
    frontier_base: Frontier[Node[int], Node[int]] = frontier
    result = run_search(FailStrategy(), frontier_base, beam_width=1)
    assert result is frontier
    assert frontier.take_calls == [1]


def test_continue_search_asserts_explore_width_positive() -> None:
    """Ensure explore_width must be positive (assertion guard)."""
    frontier = StaticFrontier([None])
    frontier_base: Frontier[Node[int], Node[int]] = frontier
    with pytest.raises(AssertionError):
        run_search(FailStrategy(), frontier_base, explore_width=0)


def test_continue_search_passes_beam_width_to_take() -> None:
    """Ensure beam_width controls the count passed into take()."""
    frontier = StaticFrontier([None])
    frontier_base: Frontier[Node[int], Node[int]] = frontier
    run_search(FailStrategy(), frontier_base, beam_width=3)
    assert frontier.take_calls == [3]

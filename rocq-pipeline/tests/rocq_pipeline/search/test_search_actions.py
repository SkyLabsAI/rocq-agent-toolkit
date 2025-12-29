"""Tests for action key handling in search."""

from __future__ import annotations

from collections.abc import Callable
from typing import override

from rocq_pipeline.search.action import Action
from rocq_pipeline.search.search.frontier import Frontier
from rocq_pipeline.search.search.search import Node

from .util import FixedStrategy, OneShotFrontier, run_search


class KeyedAction(Action[int]):
    """Action with an explicit key and recorded execution tag."""

    def __init__(self, key: str, tag: str, on_record: Callable[[str], None]) -> None:
        self._key = key
        self._tag = tag
        self._on_record = on_record

    @override
    def interact(self, state: int) -> int:
        self._on_record(self._tag)
        return state

    def key(self) -> str:
        return self._key


def test_action_dedup_per_node() -> None:
    """Ensure duplicate action keys are skipped within the same node."""
    record: list[str] = []
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        0: [
            (0.9, KeyedAction("dup", "first", record.append)),
            (0.8, KeyedAction("dup", "second", record.append)),
        ]
    }
    strategy = FixedStrategy(actions)
    frontier = OneShotFrontier([Node(0, None)])

    frontier_base: Frontier[Node[int], Node[int]] = frontier
    run_search(strategy, frontier_base, beam_width=1, explore_width=2)

    assert record == ["first"]


def test_action_key_stripping() -> None:
    """Ensure action keys are normalized by stripping whitespace."""
    record: list[str] = []
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        0: [
            (0.9, KeyedAction("  trim  ", "first", record.append)),
            (0.8, KeyedAction("trim", "second", record.append)),
        ]
    }
    strategy = FixedStrategy(actions)
    frontier = OneShotFrontier([Node(0, None)])

    frontier_base: Frontier[Node[int], Node[int]] = frontier
    run_search(strategy, frontier_base, beam_width=1, explore_width=2)

    assert record == ["first"]


def test_action_key_allowed_across_nodes() -> None:
    """Ensure identical action keys can be used on different nodes."""
    record: list[str] = []
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        0: [(0.9, KeyedAction("same", "node0", record.append))],
        1: [(0.8, KeyedAction("same", "node1", record.append))],
    }
    strategy = FixedStrategy(actions)
    frontier = OneShotFrontier([Node(0, None), Node(1, None)])

    frontier_base: Frontier[Node[int], Node[int]] = frontier
    run_search(strategy, frontier_base, beam_width=2, explore_width=2)

    assert record == ["node0", "node1"]

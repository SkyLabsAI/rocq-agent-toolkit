"""Tests for action key handling in search."""

from __future__ import annotations

from collections.abc import Callable
from typing import override

import pytest
from pyroof_search.action import Action
from pyroof_search.search.search import Node

from .util import FixedStrategy, OneShotFrontier, run_search


class KeyedAction(Action[int]):
    """Action with an explicit key and recorded execution tag."""

    def __init__(self, key: str, tag: str, record: Callable[[str], None]) -> None:
        self._key = key
        self._tag = tag
        self._record = record

    @override
    async def interact(self, state: int) -> int:
        self._record(self._tag)
        return state

    def key(self) -> str:
        return self._key


@pytest.mark.asyncio
async def test_action_dedup_per_node() -> None:
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

    await run_search(strategy, frontier, beam_width=1, explore_width=2)

    assert record == ["first"]


@pytest.mark.asyncio
async def test_action_key_stripping() -> None:
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

    await run_search(strategy, frontier, beam_width=1, explore_width=2)

    assert record == ["first"]


@pytest.mark.asyncio
async def test_action_key_allowed_across_nodes() -> None:
    """Ensure identical action keys can be used on different nodes."""
    record: list[str] = []
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        0: [(0.9, KeyedAction("same", "node0", record.append))],
        1: [(0.8, KeyedAction("same", "node1", record.append))],
    }
    strategy = FixedStrategy(actions)
    frontier = OneShotFrontier([Node(0, None), Node(1, None)])

    await run_search(strategy, frontier, beam_width=2, explore_width=2)

    assert record == ["node0", "node1"]

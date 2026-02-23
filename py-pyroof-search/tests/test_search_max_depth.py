"""Tests for max_depth gating in search."""

from __future__ import annotations

import pytest
from pyroof_search.action import Action
from pyroof_search.search.search import Node

from .util import FixedStrategy, RecordingAction, run_search, seeded_bfs

pytestmark = pytest.mark.asyncio


async def test_max_depth_blocks_deeper_nodes() -> None:
    """Ensure nodes deeper than max_depth are skipped while depth==max_depth proceeds."""
    record: list[str] = []
    root = Node(0, None)
    depth_one = Node(1, root, action_key="d1")
    depth_two = Node(2, depth_one, action_key="d2")
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        depth_one.state: [(0.9, RecordingAction("d1", record.append))],
        depth_two.state: [(0.8, RecordingAction("d2", record.append))],
    }
    strategy = FixedStrategy(actions)
    frontier = await seeded_bfs([depth_one, depth_two])
    await run_search(strategy, frontier, beam_width=2, explore_width=2, max_depth=1)

    assert record == ["d1"]

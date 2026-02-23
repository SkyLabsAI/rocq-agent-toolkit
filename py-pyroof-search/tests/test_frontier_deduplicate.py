"""Tests for the Deduplicate frontiers."""

from __future__ import annotations

import pytest
from pyroof_search.search.frontier import BFS, Deduplicate, DeduplicateWithKey


@pytest.mark.asyncio
async def test_deduplicate_drops_duplicates() -> None:
    """Verify Deduplicate drops equivalent states. Only the first instance should be queued."""
    base = BFS[int]()
    frontier = Deduplicate(base, cmp=lambda a, b: a == b)
    await frontier.push(1, None)
    await frontier.push(2, None)
    await frontier.push(1, None)
    taken = await base.take(10)
    states = [state for state, _ in taken] if taken else []
    assert states == [1, 2]


@pytest.mark.asyncio
async def test_deduplicate_clear_resets() -> None:
    """Ensure Deduplicate clear resets the seen state. A fresh run should accept prior values."""
    base = BFS[int]()
    frontier = Deduplicate(base, cmp=lambda a, b: a == b)
    await frontier.push(1, None)
    await frontier.clear()
    await frontier.push(1, None)
    taken = await base.take(10)
    states = [state for state, _ in taken] if taken else []
    assert states == [1]


@pytest.mark.asyncio
async def test_deduplicate_key_drops_duplicates() -> None:
    """Verify DeduplicateWithKey drops states with the same key. Keys define equivalence, not identity."""
    base = BFS[int]()
    frontier = DeduplicateWithKey(base, key=lambda v: v % 2)
    await frontier.push(1, None)
    await frontier.push(2, None)
    await frontier.push(3, None)
    taken = await base.take(10)
    states = [state for state, _ in taken] if taken else []
    assert states == [1, 2]


@pytest.mark.asyncio
async def test_deduplicate_key_clear_resets() -> None:
    """Ensure DeduplicateWithKey clear resets the seen keys. A fresh run should accept prior keys."""
    base = BFS[int]()
    frontier = DeduplicateWithKey(base, key=lambda v: v % 2)
    await frontier.push(1, None)
    await frontier.clear()
    await frontier.push(1, None)
    taken = await base.take(10)
    states = [state for state, _ in taken] if taken else []
    assert states == [1]

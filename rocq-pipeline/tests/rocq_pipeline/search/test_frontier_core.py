"""Baseline interface tests for frontier implementations."""

from __future__ import annotations

import pytest
from rocq_pipeline.search.search.frontier import BFS, DFS


@pytest.mark.asyncio
async def test_take_empty_returns_none() -> None:
    """Ensure empty frontiers return None on take. This matches the search loop termination contract."""
    assert not await DFS[int]().take(1)
    assert not await BFS[int]().take(1)

"""Tests for the SavingSolutions frontier wrapper."""

from __future__ import annotations

import pytest
from pyroof_search.search.frontier import BFS, SavingSolutions


@pytest.mark.asyncio
async def test_saving_solutions_capture() -> None:
    """Verify SavingSolutions captures solutions without stopping. This is intended when stop_on_first_solution is False."""
    base = BFS[int]()

    async def _is_solution(v: int) -> bool:
        return v % 2 == 0

    frontier = SavingSolutions(
        base,
        is_solution=_is_solution,
        stop_on_first_solution=False,
    )
    await frontier.push(1, None)
    await frontier.push(2, None)
    await frontier.push(4, None)
    assert frontier.solutions() == [2, 4]
    taken = await base.take(10)
    states = [state for state, _ in taken] if taken else []
    assert states == [1, 2, 4]


@pytest.mark.asyncio
async def test_saving_solutions_stop_on_first() -> None:
    """Verify SavingSolutions stops after the first solution. This is intended when stop_on_first_solution is True."""
    base = BFS[int]()

    async def _is_solution(v: int) -> bool:
        return v == 2

    frontier = SavingSolutions(
        base,
        is_solution=_is_solution,
        stop_on_first_solution=True,
    )
    await frontier.push(1, None)
    await frontier.push(2, None)
    await frontier.push(3, None)
    assert frontier.solutions() == [2]
    assert not await frontier.take(1)  # take always returns [] after a solution.


@pytest.mark.asyncio
async def test_saving_solutions_clear_resets() -> None:
    """Ensure SavingSolutions clear resets stop state and solutions. A fresh run should not inherit prior results."""
    base = BFS[int]()

    async def _is_solution(v: int) -> bool:
        return v == 1

    frontier = SavingSolutions(
        base,
        is_solution=_is_solution,
        stop_on_first_solution=True,
    )
    await frontier.push(1, None)
    assert frontier.solutions() == [1]
    await frontier.clear()
    assert frontier.solutions() == []
    await frontier.push(2, None)
    taken = await base.take(10)
    states = [state for state, _ in taken]
    assert states == [2]

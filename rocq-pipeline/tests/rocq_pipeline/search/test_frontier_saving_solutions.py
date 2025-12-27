"""Tests for the SavingSolutions frontier wrapper."""

from __future__ import annotations

from rocq_pipeline.search.search.frontier import BFS, SavingSolutions


def test_saving_solutions_capture() -> None:
    """Verify SavingSolutions captures solutions without stopping. This is intended when stop_on_first_solution is False."""
    base = BFS[int]()
    frontier = SavingSolutions(
        base,
        is_solution=lambda v: v % 2 == 0,
        stop_on_first_solution=False,
    )
    frontier.push(1, None)
    frontier.push(2, None)
    frontier.push(4, None)
    assert frontier.solutions() == [2, 4]
    taken = base.take(10)
    states = [state for state, _ in taken] if taken else []
    assert states == [1, 2, 4]


def test_saving_solutions_stop_on_first() -> None:
    """Verify SavingSolutions stops after the first solution. This is intended when stop_on_first_solution is True."""
    base = BFS[int]()
    frontier = SavingSolutions(
        base,
        is_solution=lambda v: v == 2,
        stop_on_first_solution=True,
    )
    frontier.push(1, None)
    frontier.push(2, None)
    frontier.push(3, None)
    assert frontier.solutions() == [2]
    assert frontier.take(1) is None
    taken = base.take(10)
    states = [state for state, _ in taken] if taken else []
    assert states == [1]


def test_saving_solutions_clear_resets() -> None:
    """Ensure SavingSolutions clear resets stop state and solutions. A fresh run should not inherit prior results."""
    base = BFS[int]()
    frontier = SavingSolutions(
        base,
        is_solution=lambda v: v == 1,
        stop_on_first_solution=True,
    )
    frontier.push(1, None)
    assert frontier.solutions() == [1]
    frontier.clear()
    assert frontier.solutions() == []
    frontier.push(2, None)
    taken = base.take(10)
    states = [state for state, _ in taken] if taken else []
    assert states == [2]

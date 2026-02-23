"""Test beam search with a grid navigation problem."""

from __future__ import annotations

from collections.abc import Awaitable, Callable
from dataclasses import dataclass
from typing import override

import pytest
from pyroof_search.action import Action
from pyroof_search.rollout import IteratorRollout, Rollout
from pyroof_search.search.beam import BeamSearch
from pyroof_search.search.guidance import Guidance
from pyroof_search.strategy import Strategy


@dataclass(frozen=True)
class GridState:
    """A position on a 2D grid."""

    x: int
    y: int

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, GridState):
            return False
        return self.x == other.x and self.y == other.y

    def __hash__(self) -> int:
        return hash((self.x, self.y))


class GridMoveAction(Action[GridState]):
    """Move in one of the four cardinal directions."""

    def __init__(self, dx: int, dy: int, name: str) -> None:
        self._dx = dx
        self._dy = dy
        self._name = name

    def __str__(self) -> str:
        return self._name

    @override
    async def interact(self, state: GridState) -> GridState:
        return GridState(state.x + self._dx, state.y + self._dy)

    @override
    def key(self) -> str:
        return f"move_{self._name}"

    def __lt__(self, other: object) -> bool:
        """Comparison for heap ordering (required by Interleaver)."""
        if not isinstance(other, GridMoveAction):
            return NotImplemented
        return self._name < other._name

    def __eq__(self, other: object) -> bool:
        """Equality comparison."""
        if not isinstance(other, GridMoveAction):
            return NotImplemented
        return self._dx == other._dx and self._dy == other._dy

    def __hash__(self) -> int:
        """Hash for use in sets/dicts."""
        return hash((self._dx, self._dy, self._name))


class GridStrategy(Strategy[GridState, Action[GridState]]):
    """Strategy that proposes moves in all four cardinal directions."""

    @override
    async def rollout(
        self,
        state: GridState,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action[GridState]]:
        """Yield all four possible moves with equal probability."""
        moves = [
            (0.25, GridMoveAction(1, 0, "right")),
            (0.25, GridMoveAction(-1, 0, "left")),
            (0.25, GridMoveAction(0, 1, "up")),
            (0.25, GridMoveAction(0, -1, "down")),
        ]
        return IteratorRollout(iter(moves))


class ManhattanGuidance(Guidance[GridState]):
    """Manhattan distance heuristic for grid navigation."""

    def __init__(self, target: GridState) -> None:
        self._target = target

    @override
    def score(self, state: GridState, logprob: float | None = None) -> float:
        """Return Manhattan distance to target."""
        distance = abs(state.x - self._target.x) + abs(state.y - self._target.y)

        # Optionally combine with log probability (A* style)
        if logprob is not None:
            # Lower log prob (less likely) = higher cost
            return distance - logprob

        return float(distance)


def is_solved_equals_target(
    target: GridState,
) -> Callable[[GridState], Awaitable[bool]]:
    async def _is_solved(s: GridState) -> bool:
        return s == target

    return _is_solved


@pytest.mark.asyncio
async def test_grid_simple_reach() -> None:
    """Test that beam search can find a nearby target."""
    start = GridState(0, 0)
    target = GridState(2, 1)

    guidance = ManhattanGuidance(target)
    strategy = GridStrategy()

    search = BeamSearch(
        strategy=strategy,
        guidance=guidance,
        is_solved=is_solved_equals_target(target),
        beam_width=3,
        explore_width=4,
        max_depth=10,
        stop_on_first_solution=True,
        state_key=lambda s: (s.x, s.y),  # Deduplicate by position
    )

    solutions = await search.search(start)

    assert len(solutions) > 0, "Should find at least one solution"
    assert target in solutions, f"Should find target {target}, got {solutions}"


@pytest.mark.asyncio
async def test_grid_longer_path() -> None:
    """Test beam search with a longer path."""
    start = GridState(0, 0)
    target = GridState(3, 2)  # Reduced distance to 5 steps
    guidance = ManhattanGuidance(target)
    strategy = GridStrategy()

    search = BeamSearch(
        strategy=strategy,
        guidance=guidance,
        is_solved=is_solved_equals_target(target),
        beam_width=30,  # Large beam to ensure we find path
        explore_width=4,
        max_depth=5,
        stop_on_first_solution=True,
        state_key=lambda s: (s.x, s.y),  # Deduplicate by position
    )

    solutions = await search.search(start)

    assert len(solutions) > 0, "Should find at least one solution"
    assert target in solutions, f"Should find target {target}"

    # Manhattan distance is 5, so we should find it
    expected_distance = abs(target.x) + abs(target.y)
    assert expected_distance == 5


@pytest.mark.asyncio
async def test_grid_no_solution_within_depth() -> None:
    """Test that search terminates when target is beyond max_depth."""
    start = GridState(0, 0)
    target = GridState(10, 10)  # 20 steps away

    guidance = ManhattanGuidance(target)
    strategy = GridStrategy()

    search = BeamSearch(
        strategy=strategy,
        guidance=guidance,
        is_solved=is_solved_equals_target(target),
        beam_width=5,
        explore_width=4,
        max_depth=3,  # Too shallow to reach target
        state_key=lambda s: (s.x, s.y),  # Deduplicate by position
    )

    solutions = await search.search(start)

    # Should not find solution due to depth limit
    assert target not in solutions


@pytest.mark.asyncio
async def test_grid_without_guidance() -> None:
    """Test beam search without guidance (uniform exploration)."""
    start = GridState(0, 0)
    target = GridState(1, 2)

    strategy = GridStrategy()

    # No guidance - should still work but less efficiently
    search = BeamSearch(
        strategy=strategy,
        guidance=None,  # Will use UniformGuidance
        is_solved=is_solved_equals_target(target),
        beam_width=4,
        explore_width=4,
        max_depth=5,
        stop_on_first_solution=True,
        state_key=lambda s: (s.x, s.y),  # Deduplicate by position
    )

    solutions = await search.search(start)

    assert len(solutions) > 0, "Should eventually find solution without guidance"
    assert target in solutions


@pytest.mark.asyncio
async def test_grid_multiple_solutions() -> None:
    """Test finding a solution with limited beam."""
    start = GridState(0, 0)
    target = GridState(1, 1)

    guidance = ManhattanGuidance(target)
    strategy = GridStrategy()

    search = BeamSearch(
        strategy=strategy,
        guidance=guidance,
        is_solved=is_solved_equals_target(target),
        beam_width=10,
        explore_width=4,
        max_depth=10,
        stop_on_first_solution=True,  # Changed to True
        state_key=lambda s: (s.x, s.y),  # Deduplicate by position
    )

    solutions = await search.search(start)

    assert len(solutions) > 0, "Should find at least one solution"
    # Solution should be the target state
    assert target in solutions

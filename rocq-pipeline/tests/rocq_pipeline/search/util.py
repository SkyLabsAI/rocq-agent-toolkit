"""Shared helpers for search tests."""

from __future__ import annotations

from collections.abc import Callable
from typing import TypeVar, override

from rocq_pipeline.search.action import Action
from rocq_pipeline.search.search.frontier import BFS, Frontier
from rocq_pipeline.search.search.search import (
    Node,
    RepetitionPolicy,
    Search,
    StateManipulator,
)
from rocq_pipeline.search.strategy import Strategy

S = TypeVar("S")
FNode = TypeVar("FNode")


class FixedStrategy(Strategy[S]):
    """Strategy that returns fixed rollouts per state."""

    def __init__(self, mapping: dict[S, list[tuple[float, Action[S]]]]) -> None:
        self._mapping = mapping

    @override
    def rollout(
        self,
        state: S,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout[S]:
        return iter(self._mapping.get(state, []))


class RecordingAction(Action[int]):
    """Action that reports its key to a callback when executed."""

    def __init__(
        self,
        key: str,
        on_record: Callable[[str], None],
        advance_by: int = 0,
    ) -> None:
        self._key = key
        self._on_record = on_record
        self._advance_by = advance_by

    @override
    def interact(self, state: int) -> int:
        self._on_record(self._key)
        return state + self._advance_by

    def key(self) -> str:
        return self._key


def make_chain(keys: list[str]) -> Node[int]:
    """Build a node chain where each key becomes the action_key on the next node."""
    parent: Node[int] | None = None
    state = 0
    for key in keys:
        parent = Node(state, parent, action_key=key)
        state += 1
    assert parent is not None
    return parent


def seeded_bfs(candidates: list[Node[S]]) -> BFS[Node[S]]:
    """Create a BFS frontier seeded with the provided search nodes."""
    frontier: BFS[Node[S]] = BFS()
    for candidate in candidates:
        frontier.push(candidate, None)
    return frontier


def run_search(
    strategy: Strategy[S],
    worklist: Frontier[Node[S], FNode],
    beam_width: int = 1,
    explore_width: int = 1,
    repetition_policy: RepetitionPolicy | None = None,
    state_manip: StateManipulator[S] | None = None,
    max_depth: int | None = None,
) -> Frontier[Node[S], FNode]:
    """Call continue_search with a concrete Frontier instance (mypy helper)."""
    return Search.continue_search(
        strategy,
        worklist,
        beam_width=beam_width,
        explore_width=explore_width,
        repetition_policy=repetition_policy,
        state_manip=state_manip,
        max_depth=max_depth,
    )  # type: ignore[type-var]

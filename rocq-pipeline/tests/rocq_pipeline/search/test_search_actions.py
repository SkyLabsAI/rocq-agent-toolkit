"""Tests for action key handling in search."""

from __future__ import annotations

from typing import override

from rocq_pipeline.search.action import Action
from rocq_pipeline.search.search.frontier import Frontier
from rocq_pipeline.search.search.search import (
    Node,
    RepetitionPolicy,
    Search,
    StateManipulator,
)
from rocq_pipeline.search.strategy import Strategy


class KeyedAction(Action[int]):
    """Action with an explicit key and recorded execution tag."""

    def __init__(self, key: str, tag: str, record: list[str]) -> None:
        self._key = key
        self._tag = tag
        self._record = record

    @override
    def interact(self, state: int) -> int:
        self._record.append(self._tag)
        return state

    def key(self) -> str:
        return self._key


class FixedStrategy(Strategy[int]):
    """Strategy that returns fixed rollouts per state."""

    def __init__(self, mapping: dict[int, list[tuple[float, Action[int]]]]) -> None:
        self._mapping = mapping

    @override
    def rollout(
        self,
        state: int,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout[int]:
        return iter(self._mapping.get(state, []))


class OneShotFrontier(Frontier[Node[int], Node[int]]):
    """Frontier that returns candidates only once, then terminates."""

    def __init__(self, candidates: list[Node[int]]) -> None:
        self._candidates = list(candidates)
        self._taken = False

    @override
    def push(self, val: Node[int], parent: Node[int] | None) -> None:
        return None

    @override
    def repush(self, node: Node[int]) -> None:
        return None

    @override
    def clear(self) -> None:
        return None

    @override
    def take(self, count: int) -> list[tuple[Node[int], Node[int]]] | None:
        if self._taken:
            return None
        self._taken = True
        return [(node, node) for node in self._candidates[:count]]


def run_search(
    strategy: Strategy[int],
    worklist: Frontier[Node[int], Node[int]],
    beam_width: int = 1,
    explore_width: int = 1,
    repetition_policy: RepetitionPolicy | None = None,
    state_manip: StateManipulator[int] | None = None,
    max_depth: int | None = None,
) -> Frontier[Node[int], Node[int]]:
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


def test_action_dedup_per_node() -> None:
    """Ensure duplicate action keys are skipped within the same node."""
    record: list[str] = []
    actions: dict[int, list[tuple[float, Action[int]]]] = {
        0: [
            (0.9, KeyedAction("dup", "first", record)),
            (0.8, KeyedAction("dup", "second", record)),
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
            (0.9, KeyedAction("  trim  ", "first", record)),
            (0.8, KeyedAction("trim", "second", record)),
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
        0: [(0.9, KeyedAction("same", "node0", record))],
        1: [(0.8, KeyedAction("same", "node1", record))],
    }
    strategy = FixedStrategy(actions)
    frontier = OneShotFrontier([Node(0, None), Node(1, None)])

    frontier_base: Frontier[Node[int], Node[int]] = frontier
    run_search(strategy, frontier_base, beam_width=2, explore_width=2)

    assert record == ["node0", "node1"]

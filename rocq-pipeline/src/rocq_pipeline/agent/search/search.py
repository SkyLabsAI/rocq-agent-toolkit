from __future__ import annotations

import heapq
import itertools
from abc import ABC, abstractmethod
from collections.abc import Generator
from dataclasses import dataclass
from re import U
from typing import Any, Callable, Iterable, override

from rocq_doc_manager import RocqCursor
from rocq_pipeline.agent.proof.strategy import Action, Rollout, Strategy

from .frontier import Frontier


class Node:
    depth: int
    parent: Node | None
    state: RocqCursor
    _rollout: Rollout[Action[RocqCursor]] | None

    def __init__(self, state: RocqCursor, parent: Node | None) -> None:
        self.depth = 0 if parent is None else (1 + parent.depth)
        self.state = state
        self.parent = parent
        self._rollout = None

    def rollout(
        self, strategy: Strategy[RocqCursor], **kwargs
    ) -> Rollout[Action[RocqCursor]]:
        if self._rollout is None:
            self._rollout = strategy.rollout(self.state, **kwargs)
        return self._rollout

    def update_rollout(
        self, val: RocqCursor, prob: float, rollout: Rollout[Action[RocqCursor]]
    ) -> None:
        self._rollout = rollout


class Interleaver[K, T]:
    def __init__(self, mp: dict[K, Rollout[T]]) -> None:
        self._gens = mp

    def __iter__(self) -> Iterable[tuple[K, T]]:
        return self

    def __next__(self) -> tuple[K, T] | None:
        return self.next()

    def next(self) -> tuple[K, T] | None:
        raise NotImplemented

    def stop(self) -> dict[K, tuple[T | None, Rollout[T]]]:
        """
        Returns the remaining generators, i.e. those that have not
        been pulled. The result is a dictionary with items `(k, (v, vs))`.
        If `v` is not `None`, then it should be pre-pended to `vs`.

        We return things like this in case the value `v` is useful to clients.
        """
        raise NotImplemented


def interleave_continue[K, T](
    mp: dict[K, Generator[T]],
) -> Generator[tuple[K, T], bool, dict[K, tuple[T, Generator[T]]]]:
    """
    Interleaves multiple generators yielding a single generator.
    The client can stop the generator and get back a mapping for
    any non-empty iterators.

    For example, if you have `{ 1: [a,b], 2: [c,d] }`
    you might first get `a`. Then, if you stop the iterator
    (by sending `True`) then you will get {1:[b], 2:[c,d]}
    """
    gens: list[tuple[T, K, Generator[T]]] = []

    # NOTE: we need to address the problem that arises when [K] is not const
    def pull(g: Generator[T], name: K) -> None:
        nonlocal gens
        try:
            n = next(g)
            heapq.heappush(gens, (n, name, g))
        except StopIteration:
            pass

    for i, g in mp.items():
        pull(g, name=i)

    while gens:
        v, i, rest = heapq.heappop(gens)
        result = yield (i, v)
        pull(rest, name=i)
        if result:
            # stop the iterator and return the remaining
            return {name: (val, rest) for val, name, rest in gens}
    return {}


def search[T: Frontier[Node]](
    strategy: Strategy[RocqCursor],
    start: RocqCursor,
    frontier: type[T],
    beam_width: int = 1,
    explore_width: int = 1,
) -> T:
    assert explore_width > 0

    worklist: T = frontier()
    worklist.push(Node(start, None))

    while True:
        # Sample the beam width from the frontier
        candidates = worklist.take(count=beam_width)
        if not candidates:
            # Terminate if there are no candidates.
            # This implies that the frontier is empty
            return worklist

        # Rollout each node in the tree
        stream = Interleaver(
            {
                nm: val.rollout(strategy, max_rollout=explore_width)
                for nm, val in enumerate(candidates)
            }
        )

        def process(candidate: Node, action: Action[RocqCursor]) -> None:
            fresh_cursor = candidate.state.clone()
            try:
                next_state = action.step(fresh_cursor)
                new_node = Node(next_state, candidate)
                worklist.push(new_node)
            except Action.FailedAction:
                fresh_cursor.dispose()

        # Due to the way that generators work, we can not send a message to the first element
        # so we need to special case this logic
        for candidate, action in itertools.islice(stream, explore_width):
            process(candidates[candidate], action)

        # NOTE: this breaks the "beam-style" frontier where only
        # nodes at a particular depth are selected
        for candidate, rest in remaining.value.items():
            cand = candidates[candidate]
            cand.update_rollout(rest)
            worklist.push(cand)

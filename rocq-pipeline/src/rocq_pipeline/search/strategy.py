from __future__ import annotations

import heapq
from abc import ABC, abstractmethod
from collections.abc import Generator, Mapping
from typing import Any, override

from .action import Action


class Strategy[T](ABC):
    """
    A `Strategy` proposes actions to take. The different proposals
    are captured lazily using a `Generator`. This allows capturing
    very large (even infinite) action spaces such as next tactic
    prediction in theorem proving.
    """

    # TODO: make [Rollout] into a class
    type Rollout[U] = Generator[tuple[float, Action[U]]]

    # Context information must be read-only and constant in order
    # for searches to work correctly. Clients should use an
    # implementation such as `immutabledict` to achieve this.
    # Mutable information needs to be tracked in the state
    type Context = Mapping[str, Any]

    @abstractmethod
    def rollout(
        self,
        state: T,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[T]:
        """
        Given the goal `G`, generates `(Pr,A)` such that:
        - `Pr` is the probability that `A` is (the next/a necessary) step in an
            efficient proof of `G`

        Notes:
        - If a strategy does not apply, it should produce an empty generator.
        - The returned generator **must** return results with decreasing
            probability since clients will generally not ask for a new `Action`
            unless the previous one did not work.
        """
        pass


def empty_Rollout() -> Strategy.Rollout:
    yield from ()


class CompositeStrategy[T](Strategy[T]):
    """A (fair) combination of strategies"""

    def __init__(self, children: list[Strategy[T]]) -> None:
        self._children: list[Strategy[T]] = children

    @override
    def rollout(
        self,
        state: T,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout:
        def combine() -> Strategy.Rollout:
            queue: list[tuple[float, int, Action[T], Strategy.Rollout]] = []
            for i, strat in enumerate(self._children):
                gen = strat.rollout(rdm, max_rollout=max_rollout, context=context)
                try:
                    pr, act = next(gen)
                except StopIteration:
                    continue
                heapq.heappush(queue, (pr, i, act, gen))

            while True:
                try:
                    (pr, i, act, gen) = heapq.heappop(queue)
                except IndexError:
                    return
                yield (pr, act)
                try:
                    pr, act = next(gen)
                except StopIteration:
                    continue
                heapq.heappush(queue, (pr, i, act, gen))

        return combine()


class FailStrategy[T](Strategy[T]):
    """A simple strategy that fails."""

    @override
    def rollout(
        self,
        state: T,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout:
        return empty_Rollout()


class GuardStrategy[T, With](FailStrategy[T], ABC):
    """Guard the execution of a strategy.
    If [check] returns [None], then this strategy acts like the [FailStrategy] otherwise
    it does [rollout_with]
    """

    @abstractmethod
    def check(
        self, state: T, context: Strategy.Context | None = None
    ) -> With | None: ...

    @abstractmethod
    def rollout_with(
        self,
        val: With,
        rdm: T,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout: ...

    @override
    def rollout(
        self,
        state: T,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout:
        val = self.check(state)
        if val is None:
            return super().rollout(state, max_rollout, context)
        return self.rollout_with(val, state, max_rollout, context)

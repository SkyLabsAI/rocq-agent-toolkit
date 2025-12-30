from __future__ import annotations

import heapq
from abc import ABC, abstractmethod
from collections.abc import Callable, Iterable, Mapping
from typing import Any, TypeVar, override

from .action import Action
from .rollout import (
    EmptyRollout,
    InterleaveRollout,
    IteratorRollout,
    Rollout,
    SingletonRollout,
)

T_co = TypeVar("T_co", covariant=True)


class Strategy[T_co](ABC):
    """
    A `Strategy` proposes actions to take. The different proposals
    are captured lazily using a `Generator`. This allows capturing
    very large (even infinite) action spaces such as next tactic
    prediction in theorem proving.
    """

    # Context information must be read-only and constant in order
    # for searches to work correctly. Clients should use an
    # implementation such as `immutabledict` to achieve this.
    # Mutable information needs to be tracked in the state
    type Context = Mapping[str, Any]

    @abstractmethod
    def rollout(
        self,
        state: T_co,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action[T_co]]:
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


class SingletonStrategy[T_co](Strategy[T_co]):
    def __init__(self, value: Action[T_co], logprob: float = 1.0) -> None:
        self._value = value
        self._logprob = logprob

    def rollout(
        self,
        state: T_co,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action[T_co]]:
        return SingletonRollout(self._value, logprob=self._logprob)


class IteratorStrategy[T_co](Strategy[T_co]):
    def __init__(self, i: Iterable[tuple[float, Action[T_co]]]) -> None:
        self._collection = i

    def rollout(
        self,
        state: T_co,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action[T_co]]:
        return IteratorRollout(
            (Rollout.Approx(logprob, act) for logprob, act in self._collection)
        )


class CompositeStrategy[T_co](Strategy[T_co]):
    """A (fair) combination of strategies"""

    def __init__(self, children: list[Strategy[T_co]]) -> None:
        self._children: list[Strategy[T_co]] = children

    @override
    def rollout(
        self,
        state: T_co,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action[T_co]]:
        return InterleaveRollout(
            [
                strat.rollout(state, max_rollout, context=context)
                for strat in self._children
            ]
        )


class FailStrategy[T_co](Strategy[T_co]):
    """A simple strategy that fails."""

    @override
    def rollout(
        self,
        state: T_co,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action[T_co]]:
        return EmptyRollout()


class GuardStrategy[T_co, With](FailStrategy[T_co], ABC):
    """Guard the execution of a strategy.
    If [check] returns [None], then this strategy acts like the [FailStrategy] otherwise
    it does [rollout_with]
    """

    @abstractmethod
    def check(
        self, state: T_co, context: Strategy.Context | None = None
    ) -> With | None: ...

    @abstractmethod
    def rollout_with(
        self,
        val: With,
        rdm: T_co,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action[T_co]]: ...

    @override
    def rollout(
        self,
        state: T_co,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action[T_co]]:
        val = self.check(state)
        if val is None:
            return super().rollout(state, max_rollout, context)
        return self.rollout_with(val, state, max_rollout, context)


# class TraceStrategy[T_co](Strategy[T_co]):
#     def __init__(self, base: Strategy[T_co]) -> None:
#         self._base = base
#         self._trace: list[tuple[T_co, Action[T_co]]] = []

#     @property
#     def trace(self) -> list[tuple[T_co, Action[T_co]]]:
#         return self._trace

#     @override
#     def rollout(
#         self,
#         state: T_co,
#         max_rollout: int | None = None,
#         context: Strategy.Context | None = None,
#     ) -> Rollout[T_co]:
#         roll = self._base.rollout(state, max_rollout, context)

#         def mk(action: Action[T_co]) -> Callable[[T_co], None]:
#             def fn(state: T_co) -> None:
#                 self._trace.append((state, action))

#             return fn

#         return IteratorRollout(
#             ((prob, ActionWrapper(action, mk(action))) for prob, action in roll)
#         )

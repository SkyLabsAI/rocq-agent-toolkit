from __future__ import annotations

import heapq
from abc import ABC, abstractmethod
from collections.abc import Callable, Iterable, Iterator, Mapping
from dataclasses import dataclass
from typing import Any, TypeVar, override

from .action import Action

T_co = TypeVar("T_co", covariant=True)


class Rollout[T_co](ABC):
    """
    This type is effectively: Iterator[Rollout.Delay | Rollout.Result]
    """

    @dataclass(frozen=True)
    class Delay[U]:
        logprob: float

    @dataclass(frozen=True)
    class Result[U]:
        logprob: float
        result: Action[U]

    @abstractmethod
    def next(
        self, min_logprob: float = -float("inf")
    ) -> Rollout.Delay | Rollout.Result:
        """
        strat.next(min_prob=math.log(0.5))
        - Rollout.Delay(math.log(0.45)) -- i don't have anything with higher prob than 0.5, ask me again when you want something less 0.45
        - Rollout.Result(math.log(0.6), act) -- action has probability 0.6

        An implementation is only allowed to return `Delay(Pr)` if `Pr < min_logprob`, otherwise, it must produce a value, or raise `StopIteration`.

        raises `StopIteration` when complete
        """
        ...

    def __next__(self) -> tuple[float, Action[T_co]]:
        result = self.next()
        assert isinstance(result, Rollout.Result)
        return (result.logprob, result.result)


class EmptyRollout[T_co](Rollout[T_co]):
    @override
    def next(self, min_prob: float = 0) -> Rollout.Delay | Rollout.Result:
        raise StopIteration()


def empty_Rollout[T]() -> Rollout[T]:
    return EmptyRollout()


class SingletonRollout[T_co](Rollout[T_co]):
    def __init__(
        self,
        value: Action[T_co],
        *,
        logprob: float = 0.0,
    ) -> None:
        assert logprob <= 0  # validation logic?
        self._value = value
        self._logprob = logprob
        self._done = False

    @override
    def next(self, min_logprob: float = 0) -> Rollout.Delay | Rollout.Result[T_co]:
        if self._done:
            raise StopIteration()
        if min_logprob > self._logprob:
            return Rollout.Delay(self._logprob)
        else:
            self._done = True
            return Rollout.Result(self._logprob, self._value)


class IterableRollout[T_co](Rollout[T_co]):
    def __init__(self, iterable: Iterable[tuple[float, Action[T_co]]]) -> None:
        self._values = iter(iterable)

    @override
    def next(self, min_logprob: float = 0) -> Rollout.Delay | Rollout.Result:
        logprob, act = next(self._values)
        return Rollout.Result(logprob, act)


class IteratorRollout[T_co](Rollout[T_co]):
    def __init__(self, iterator: Iterator[Rollout.Delay | Rollout.Result]) -> None:
        self._values = iterator
        self._last: float | None = None

    def next(
        self, min_logprob: float = -float("inf")
    ) -> Rollout.Delay | Rollout.Result:
        if self._last is not None and min_logprob > self._last:
            return Rollout.Delay(self._last)
        result = next(self._values)
        if isinstance(result, Rollout.Delay):
            self._last = (
                result.logprob
                if self._last is None
                else min(self._last, result.logprob)
            )
            # recursive call, but we consumed one value out of the generator
            return self.next(min_logprob=min_logprob)
        assert isinstance(result, Rollout.Result)
        self._last = result.logprob
        return result


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
    ) -> Rollout[T_co]:
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
    ) -> Rollout[T_co]:
        return SingletonRollout(self._value, logprob=self._logprob)


class IteratorStrategy[T_co](Strategy[T_co]):
    def __init__(self, i: Iterable[tuple[float, Action[T_co]]]) -> None:
        self._collection = i

    def rollout(
        self,
        state: T_co,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[T_co]:
        return IteratorRollout(
            (Rollout.Result(logprob, act) for logprob, act in self._collection)
        )


class CompositeStrategy[T_co](Strategy[T_co]):
    """A (fair) combination of strategies"""

    def __init__(self, children: list[Strategy[T_co]]) -> None:
        self._children: list[Strategy[T_co]] = children

    class Rollout[U](Rollout[U]):
        class Node[V]:
            def __init__(
                self,
                logprob: float,
                owner: int,
                action: Action[V] | None,
                rest: Rollout[V],
            ) -> None:
                self.logprob = logprob
                self.owner = owner
                self.action = action
                self.rest = rest

            def __lt__(self, other: CompositeStrategy.Rollout.Node[V]) -> bool:
                # Note, since we are using `heapq` (which yields the smallest first)
                # we make sure that we return the largest first
                if self.logprob != other.logprob:
                    return other.logprob < self.logprob
                if self.action is not None and other.action is None:
                    return True
                if self.action is None and other.action is None:
                    return False
                return self.owner < other.owner

        def __init__(self, children: list[Rollout[U]]) -> None:
            self._queue: list[CompositeStrategy.Rollout.Node[U]] = []

            for i, rollout in enumerate(children):
                # We pass 0.0 as the highest probability to allow `Strategy`s
                # to only advertise their certainty
                self._push_next(i, rollout, 0.0)

        def _push_next(self, i: int, rollout: Rollout[U], min_logprob=0.0) -> float:
            try:
                result = rollout.next(min_logprob)
            except StopIteration:
                return min_logprob
            heapq.heappush(
                self._queue,
                CompositeStrategy.Rollout.Node(
                    result.logprob,
                    i,
                    result.result if isinstance(result, Rollout.Result) else None,
                    rollout,
                ),
            )
            return result.logprob

        @override
        def next(
            self, min_logprob: float = -float("inf")
        ) -> Rollout.Delay | Rollout.Result:
            # All entries inside this will have `action = None`
            # Also, the highest item will be first
            stashed: list[CompositeStrategy.Rollout.Node[U]] = []
            candidate: CompositeStrategy.Rollout.Node[U] | None = None
            while True:
                try:
                    result = heapq.heappop(self._queue)
                except IndexError:
                    break

                if result.action is None:
                    if result.logprob < min_logprob:
                        # This is the highest node and it has a probability less than the query
                        heapq.heappush(self._queue, result)
                        break
                    else:
                        # There might be a lower probability value that we need to yield, so
                        # we stash this node and try to find the next node
                        stashed.append(result)
                        continue
                else:
                    heapq.heappush(self._queue, result)
                    candidate = result
                    break

            # TODO: Find the highest action in stashed and candidate (down to `min_logprob`)
            #
            highest = candidate.logprob if candidate is not None else min_logprob
            for n in stashed:
                try:
                    xxx = n.rest.next(highest)
                except StopIteration:
                    continue
                if isinstance(xxx, Rollout.Result):
                    if candidate is None:
                        candidate = CompositeStrategy.Rollout.Node(
                            xxx.logprob,
                            n.owner,
                            xxx.result,
                            n.rest,
                        )
                        highest = candidate.logprob
                    elif xxx.logprob > candidate.logprob:
                        heapq.heappush(self._queue, candidate)
                        candidate = CompositeStrategy.Rollout.Node(
                            xxx.logprob,
                            n.owner,
                            xxx.result,
                            n.rest,
                        )
                        highest = candidate.logprob
                    else:
                        heapq.heappush(
                            self._queue,
                            CompositeStrategy.Rollout.Node(
                                xxx.logprob, n.owner, xxx.result, n.rest
                            ),
                        )
                else:
                    heapq.heappush(
                        self._queue,
                        CompositeStrategy.Rollout.Node(
                            xxx.logprob, n.owner, None, n.rest
                        ),
                    )
            if candidate:
                assert candidate.action is not None
                return Rollout.Result(candidate.logprob, candidate.action)
            else:
                return Rollout.Delay(highest)

    @override
    def rollout(
        self,
        state: T_co,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[T_co]:
        return CompositeStrategy.Rollout(
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
    ) -> Rollout[T_co]:
        return empty_Rollout()


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
    ) -> Rollout[T_co]: ...

    @override
    def rollout(
        self,
        state: T_co,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[T_co]:
        val = self.check(state)
        if val is None:
            return super().rollout(state, max_rollout, context)
        return self.rollout_with(val, state, max_rollout, context)


class ActionWrapper[T_co](Action[T_co]):
    def __init__(self, base: Action[T_co], fn: Callable[[T_co], None]) -> None:
        self._fn = fn
        self._base = base

    def interact(self, state: T_co) -> T_co:
        self._fn(state)
        return self._base.interact(state)


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

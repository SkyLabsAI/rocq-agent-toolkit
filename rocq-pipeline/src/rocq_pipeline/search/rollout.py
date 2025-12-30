from __future__ import annotations

import heapq
from abc import ABC, abstractmethod
from collections.abc import Callable, Iterable, Iterator, Mapping
from dataclasses import dataclass
from typing import Any, TypeVar, override

from .action import Action

NEG_INF = -float("inf")

T_co = TypeVar("T_co", covariant=True)
U_co = TypeVar("U_co", covariant=True)


class Rollout[T_co](ABC):
    """
    This type is effectively: Iterator[Rollout.Delay | Rollout.Result]
    """

    @dataclass(frozen=True)
    class Approx[U_co]:
        logprob: float
        result: U_co | None

    @abstractmethod
    def next(self, min_logprob: float = NEG_INF) -> Rollout.Approx[T_co]:
        """
        strat.next(min_prob=math.log(0.5))
        - Rollout.Delay(math.log(0.45)) -- i don't have anything with higher prob than 0.5, ask me again when you want something less 0.45
        - Rollout.Result(math.log(0.6), act) -- action has probability 0.6

        An implementation is only allowed to return `Delay(Pr)` if `Pr < min_logprob`, otherwise, it must produce a value, or raise `StopIteration`.

        raises `StopIteration` when complete
        """
        ...

    def __next__(self) -> tuple[float, T_co]:
        result = self.next()
        assert result.result is not None
        return (result.logprob, result.result)

    def __iter__(self) -> Iterator[tuple[float, T_co]]:
        return self


class EmptyRollout[T_co](Rollout[T_co]):
    @override
    def next(self, min_logprob: float = NEG_INF) -> Rollout.Approx[T_co]:
        raise StopIteration()


def empty_Rollout[T]() -> Rollout[T]:
    return EmptyRollout()


class ConsRollout[T_co](Rollout[T_co]):
    def __init__(self, value: T_co, logprob: float, rest: Rollout[T_co]) -> None:
        assert logprob <= 0  # validation logic?
        self._value = value
        self._logprob = logprob
        self._done = False
        self._rest = rest

    def next(self, min_logprob: float = NEG_INF) -> Rollout.Approx[T_co]:
        if self._done:
            return self._rest.next(min_logprob=min_logprob)
        if min_logprob > self._logprob:
            return Rollout.Approx(self._logprob, None)
        else:
            self._done = True
            return Rollout.Approx(self._logprob, self._value)


class SingletonRollout[T_co](Rollout[T_co]):
    def __init__(
        self,
        value: T_co,
        *,
        logprob: float = 0.0,
    ) -> None:
        assert logprob <= 0  # validation logic?
        self._value = value
        self._logprob = logprob
        self._done = False

    @override
    def next(self, min_logprob: float = NEG_INF) -> Rollout.Approx[T_co]:
        if self._done:
            raise StopIteration()
        if min_logprob > self._logprob:
            return Rollout.Approx(self._logprob, None)
        else:
            self._done = True
            return Rollout.Approx(self._logprob, self._value)


class IterableRollout[T_co](Rollout[T_co]):
    def __init__(self, iterable: Iterable[tuple[float, T_co]]) -> None:
        self._values = iter(iterable)

    @override
    def next(self, min_logprob: float = 0) -> Rollout.Approx[T_co]:
        logprob, act = next(self._values)
        return Rollout.Approx(logprob, act)


class IteratorRollout[T_co](Rollout[T_co]):
    def __init__(self, iterator: Iterator[Rollout.Approx[T_co]]) -> None:
        self._values = iterator
        self._last: float | None = None

    def next(self, min_logprob: float = -float("inf")) -> Rollout.Approx[T_co]:
        if self._last is not None and min_logprob > self._last:
            return Rollout.Approx(self._last, None)
        result = next(self._values)
        if result.result is None:
            self._last = (
                result.logprob
                if self._last is None
                else min(self._last, result.logprob)
            )
            # recursive call, but we consumed one value out of the generator
            return self.next(min_logprob=min_logprob)
        self._last = result.logprob
        return result


class MapRollout[T_co, U](Rollout[U]):
    def __init__(self, base: Rollout[T_co], fn: Callable[[T_co], U]) -> None:
        self._base = base
        self._fn = fn

    @override
    def next(self, min_logprob: float = NEG_INF) -> Rollout.Approx[U]:
        result = self._base.next(min_logprob=min_logprob)
        if result.result is None:
            return Rollout.Approx(result.logprob, None)
        else:
            return Rollout.Approx(result.logprob, self._fn(result.result))


class InterleaveRollout[U](Rollout[U]):
    class Node[V]:
        def __init__(
            self,
            logprob: float,
            owner: int,
            action: V | None,
            rest: Rollout[V],
        ) -> None:
            self.logprob = logprob
            self.owner = owner
            self.action = action
            self.rest = rest

        def __lt__(self, other: InterleaveRollout.Node[V]) -> bool:
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
        self._queue: list[InterleaveRollout.Node[U]] = []

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
            InterleaveRollout.Node(
                result.logprob,
                i,
                result.result,
                rollout,
            ),
        )
        return result.logprob

    @override
    def next(self, min_logprob: float = -float("inf")) -> Rollout.Approx[U]:
        # All entries inside this will have `action = None`
        # Also, the highest item will be first
        stashed: list[InterleaveRollout.Node[U]] = []
        candidate: InterleaveRollout.Node[U] | None = None
        highest: float = min_logprob
        while True:
            try:
                result = heapq.heappop(self._queue)
            except IndexError:
                break

            highest = result.logprob
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
        for n in stashed:
            try:
                xxx = n.rest.next(highest)
            except StopIteration:
                continue
            if xxx.result is not None:
                if candidate is None:
                    candidate = InterleaveRollout.Node(
                        xxx.logprob,
                        n.owner,
                        xxx.result,
                        n.rest,
                    )
                    highest = candidate.logprob
                elif xxx.logprob > candidate.logprob:
                    heapq.heappush(self._queue, candidate)
                    candidate = InterleaveRollout.Node(
                        xxx.logprob,
                        n.owner,
                        xxx.result,
                        n.rest,
                    )
                    highest = candidate.logprob
                else:
                    heapq.heappush(
                        self._queue,
                        InterleaveRollout.Node(
                            xxx.logprob, n.owner, xxx.result, n.rest
                        ),
                    )
            else:
                heapq.heappush(
                    self._queue,
                    InterleaveRollout.Node(xxx.logprob, n.owner, None, n.rest),
                )

        if candidate:
            assert candidate.action is not None
            return Rollout.Approx(candidate.logprob, candidate.action)
        else:
            if self._queue:
                return Rollout.Approx(highest, None)
            raise StopIteration()

    def stop(self) -> dict[int, Rollout[U]]:
        def mk(logprob: float, act: U | None, rest: Rollout[U]) -> Rollout[U]:
            if act is None:
                return rest
            else:
                return ConsRollout(act, logprob, rest)

        result = {n.owner: mk(n.logprob, n.action, n.rest) for n in self._queue}
        self._queue = []
        return result

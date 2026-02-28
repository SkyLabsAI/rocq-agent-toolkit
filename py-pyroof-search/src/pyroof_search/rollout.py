from __future__ import annotations

import heapq
from abc import ABC, abstractmethod
from collections.abc import AsyncIterator, Awaitable, Callable, Iterator
from dataclasses import dataclass, field
from typing import TypeVar, override

NEG_INF = -float("inf")

T_co = TypeVar("T_co", covariant=True)
U_co = TypeVar("U_co", covariant=True)


class Proposals[T_co](ABC):
    """Iterator over ranked _alternative_ actions.

    Elements of `Rollout` are tuples of the form `(Pr_i, Act_i)` where `Pr_i`
    is the confidence (often captured via a log probability) that `Act_i` is
    the next `Action` that should be taken to make efficient progress towards
    completing the overall task. Scores in the `Rollout` (i.e. `Pr_i`):
    - a) must be interpreted in a consistent manner between all strategies used
         to produce a given `Rollout` (often as log probabilities)
    - b) should be returned from "best" to "worst" based on (a), since clients
         will generally not ask for a new `Action` unless the previous ones did
         not work

    Every strategy is responsible for implementing `Strategy.rollout` which
    produces a (potentially infinite) `Rollout`. To avoid performance impacts
    from eagerly evaluating large rollouts (or from expensive candidate generation):
    1. implementers of `Strategy.rollout` should use generators unless the result
       is small+finite (e.g. a singleton list)
    2. clients of `Strategy.rollout` should lazily draw from `Rollout` and
       never force the full computation; i.e. DO NOT DO THE FOLLOWING:
       ```python
       # BAD: forcing a computation on a potentially infinite rollout
       for i, (_, a) in enumerate(s.rollout(...)):
           print(f"{i}: {a}")
       ```

    Example: a finite `Rollout` that contains `[(0, A_1), (-1, A_2)]`
    is saying to try `A_1` before `A_2` and associates each with
    a confidence score.

    For functional readers, this is similar to:
    ```
    Rollout[Action] := float -> tuple[float, Action | None, Rollout[Action]] | raise StopAsyncIteration
    ```
    """

    @dataclass(frozen=True)
    class Approx[U_co]:
        logprob: float = field(kw_only=True)
        result: U_co | None = field(kw_only=True, default=None)

    @abstractmethod
    async def next(self, min_logprob: float = NEG_INF) -> Proposals.Approx[T_co]:
        """
        strat.next(min_logprob=0.5) could return either:
        - Rollout.Approx(logprob=0.45, result=None) -- No new elements with higher probability
          than 0.45, ask again when you want something less than 0.45
        - Rollout.Approx(logprob=0.6, result=act) -- action has probability 0.6

        An implementation is only allowed to return `None` in the `result` field
        if `Pr < min_logprob`, otherwise, it must produce a value, or raise
        `StopAsyncIteration`.

        raises `StopAsyncIteration` when complete
        """
        ...

    async def __anext__(self) -> tuple[float, T_co]:
        result = await self.next()
        assert isinstance(result, Proposals.Approx)
        assert result.result is not None
        return (result.logprob, result.result)

    def __aiter__(self) -> AsyncIterator[tuple[float, T_co]]:
        return self


class EmptyProposals[T_co](Proposals[T_co]):
    @override
    async def next(self, min_logprob: float = NEG_INF) -> Proposals.Approx[T_co]:
        raise StopAsyncIteration()


def empty[T]() -> Proposals[T]:
    return EmptyProposals()


class ConsProposals[T_co](Proposals[T_co]):
    def __init__(self, value: T_co, logprob: float, rest: Proposals[T_co]) -> None:
        # assert logprob <= 0  # validation logic?
        self._value = value
        self._logprob = logprob
        self._done = False
        self._rest = rest

    async def next(self, min_logprob: float = NEG_INF) -> Proposals.Approx[T_co]:
        if self._done:
            return await self._rest.next(min_logprob=min_logprob)
        if min_logprob > self._logprob:
            return Proposals.Approx(logprob=self._logprob, result=None)
        else:
            self._done = True
            return Proposals.Approx(logprob=self._logprob, result=self._value)


def singleton[T_co](value: T_co, *, score: float) -> Proposals[T_co]:
    return ConsProposals(value, logprob=score, rest=empty())


class AsyncApproximatingProposals[T_co](Proposals[T_co]):
    """A rollout built from successive approximations"""

    def __init__(self, iterator: AsyncIterator[Proposals.Approx[T_co]]) -> None:
        self._values = iterator
        self._last: float | None = None

    async def next(self, min_logprob: float = NEG_INF) -> Proposals.Approx[T_co]:
        if self._last is not None and min_logprob > self._last:
            return Proposals.Approx(logprob=self._last, result=None)

        async for result in self._values:
            if result.result is None:
                self._last = (
                    result.logprob
                    if self._last is None
                    else min(self._last, result.logprob)
                )
                # recursive call, but we consumed one value out of the generator
                return await self.next(min_logprob=min_logprob)
            else:
                self._last = result.logprob
                return result
        raise StopAsyncIteration


class ApproximatingProposals[T_co](Proposals[T_co]):
    """A rollout built from successive approximations"""

    def __init__(self, iterator: Iterator[Proposals.Approx[T_co]]) -> None:
        self._values = iterator
        self._last: float | None = None

    async def next(self, min_logprob: float = NEG_INF) -> Proposals.Approx[T_co]:
        if self._last is not None and min_logprob > self._last:
            return Proposals.Approx(logprob=self._last, result=None)

        for result in self._values:
            if result.result is None:
                self._last = (
                    result.logprob
                    if self._last is None
                    else min(self._last, result.logprob)
                )
                # recursive call, but we consumed one value out of the generator
                return await self.next(min_logprob=min_logprob)
            else:
                self._last = result.logprob
                return result
        raise StopAsyncIteration


def from_iterator[T_co](iterator: Iterator[tuple[float, T_co]]) -> Proposals[T_co]:
    """Rolls out the values from the iterable.
    The scores are expected to be in decreasing order.
    """

    async def fn():
        for logprob, act in iterator:
            yield Proposals.Approx(logprob=logprob, result=act)

    return AsyncApproximatingProposals(fn())


def from_async_iterator[T_co](
    iterator: AsyncIterator[tuple[float, T_co]],
) -> Proposals[T_co]:
    """Rolls out the values from the iterable.
    The scores are expected to be in decreasing order.
    """

    return AsyncApproximatingProposals(
        Proposals.Approx(logprob=logprob, result=act) async for logprob, act in iterator
    )


class AsyncMapRollout[T_co, U_co](Proposals[U_co]):
    """Change the values of a Rollout, but not their scores"""

    def __init__(
        self, base: Proposals[T_co], fn: Callable[[T_co], Awaitable[U_co]]
    ) -> None:
        self._base = base
        self._fn = fn

    @override
    async def next(self, min_logprob: float = NEG_INF) -> Proposals.Approx[U_co]:
        result = await self._base.next(min_logprob=min_logprob)
        if result.result is None:
            return Proposals.Approx(logprob=result.logprob, result=None)
        else:
            return Proposals.Approx(
                logprob=result.logprob, result=await self._fn(result.result)
            )


def map[T_co, U_co](
    base: Proposals[T_co], fn: Callable[[T_co], U_co]
) -> Proposals[U_co]:
    """Change the values of a Rollout, but not their scores"""

    async def fn_async(x: T_co) -> U_co:
        return fn(x)

    return AsyncMapRollout(base, fn_async)


class InterleaveRollout[U_co](Proposals[U_co]):
    """Interleave the results from many rollouts in a fair way."""

    class Node[V]:
        def __init__(
            self,
            logprob: float,
            owner: int,
            action: V | None,
            rest: Proposals[V],
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

    def __init__(self, children: list[Proposals[U_co]]) -> None:
        self._queue: list[InterleaveRollout.Node[U_co]] = []
        self._delayed_init: list[Proposals[U_co]] | None = children

    async def _push_next(
        self, i: int, rollout: Proposals[U_co], min_logprob=NEG_INF
    ) -> float:
        try:
            result = await rollout.next(min_logprob)
        except StopAsyncIteration:
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
    async def next(self, min_logprob: float = NEG_INF) -> Proposals.Approx[U_co]:
        if self._delayed_init is not None:
            for i, rollout in enumerate(self._delayed_init):
                # We pass 0.0 as the highest probability to allow `Strategy`s
                # to only advertise their certainty
                await self._push_next(i, rollout, 0.0)
            self._delayed_init = None

        # All entries inside this will have `action = None`
        # Also, the highest item will be first
        stashed: list[InterleaveRollout.Node[U_co]] = []
        candidate: InterleaveRollout.Node[U_co] | None = None
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
                candidate = result
                break

        # TODO: Find the highest action in stashed and candidate (down to `min_logprob`)
        #
        for n in stashed:
            try:
                r_next = await n.rest.next(highest)
            except StopAsyncIteration:
                continue
            if r_next.result is not None:
                if candidate is None:
                    candidate = InterleaveRollout.Node(
                        r_next.logprob,
                        n.owner,
                        r_next.result,
                        n.rest,
                    )
                    highest = candidate.logprob
                elif r_next.logprob > candidate.logprob:
                    heapq.heappush(self._queue, candidate)
                    candidate = InterleaveRollout.Node(
                        r_next.logprob,
                        n.owner,
                        r_next.result,
                        n.rest,
                    )
                    highest = candidate.logprob
                else:
                    heapq.heappush(
                        self._queue,
                        InterleaveRollout.Node(
                            r_next.logprob, n.owner, r_next.result, n.rest
                        ),
                    )
            else:
                heapq.heappush(
                    self._queue,
                    InterleaveRollout.Node(r_next.logprob, n.owner, None, n.rest),
                )

        if candidate:
            assert candidate.action is not None
            await self._push_next(candidate.owner, candidate.rest)
            return Proposals.Approx(logprob=candidate.logprob, result=candidate.action)
        else:
            if self._queue:
                return Proposals.Approx(logprob=highest, result=None)
            raise StopAsyncIteration()

    def stop(self) -> dict[int, Proposals[U_co]]:
        def mk(
            logprob: float, act: U_co | None, rest: Proposals[U_co]
        ) -> Proposals[U_co]:
            if act is None:
                return rest
            else:
                return ConsProposals(act, logprob, rest)

        result = {n.owner: mk(n.logprob, n.action, n.rest) for n in self._queue}
        self._queue = []
        return result


class StagedRollout[T_co](Proposals[T_co]):
    """Interleave the results of two `Rollout`s by prioritizing the first up until some cutoff."""

    @dataclass(slots=True)
    class YieldUntil[U](Proposals[U]):
        active: Proposals[U]
        waiting: Callable[[], Awaitable[Proposals[U]]]
        cutoff: float | None
        parent: StagedRollout[U]

        @override
        async def next(self, min_logprob: float = NEG_INF) -> Proposals.Approx[U]:
            try:
                result = await self.active.next(min_logprob=min_logprob)
            except StopAsyncIteration:
                self.parent._state = await self.waiting()
                return await self.parent._state.next(min_logprob=min_logprob)

            if self.cutoff is None or result.logprob >= self.cutoff:
                assert result.result is not None or result.logprob < min_logprob
                return result
            self.parent._state = StagedRollout.Merge(
                next_pull=await self.waiting(),
                other=self.active,
                last_pull=result,
                parent=self.parent,
            )
            return await self.parent._state.next(min_logprob=min_logprob)

    @dataclass(slots=True)
    class Merge[U](Proposals[U]):
        """In this state, I need to pull from `next_pull` and compare it to `last_pull` (which came from `other`)."""

        next_pull: Proposals[U]
        other: Proposals[U]
        last_pull: Proposals.Approx[U]  # Came from other
        parent: StagedRollout[U]

        def _set(
            self,
            next_pull: Proposals[U],
            other: Proposals[U],
            last_pull: Proposals.Approx[U],
        ) -> None:
            self.next_pull = next_pull
            self.other = other
            self.last_pull = last_pull

        @override
        async def next(self, min_logprob: float = NEG_INF) -> Proposals.Approx[U]:
            try:
                result = await self.next_pull.next(min_logprob=min_logprob)
            except StopAsyncIteration:
                self.parent._state = self.other
                if self.last_pull.result is None:
                    return await self.parent._state.next(min_logprob=min_logprob)
                else:
                    return self.last_pull
            if result.logprob > self.last_pull.logprob:
                return result
            # I need to return self.last_pull before result
            if self.last_pull.result is not None:
                # last_pull has a value, so return it now, but I need to store `result`
                tresult = self.last_pull
                self._set(self.other, self.next_pull, result)
                return tresult

            # last_pull does NOT have a value
            if min_logprob > self.last_pull.logprob:
                # it is safe to yield last_pull, but i need to store [result]
                tresult = self.last_pull
                self._set(self.other, self.next_pull, result)
                return tresult
            else:
                # i can not yield last_pull, i need to query again
                try:
                    result2 = await self.other.next(min_logprob=min_logprob)
                except StopAsyncIteration:
                    # There is nothing left in self.other, and last_pull did not contain
                    # an item, so I return `result`
                    self.parent._state = self.next_pull
                    return result
                if result2.logprob > result.logprob:
                    # Going to return result2, but since result2 came from self.other
                    # i need to swap so that i can write result into last_pull
                    self._set(self.other, self.next_pull, result)
                    return result2
                else:
                    # I need to return result before I return result2
                    self.last_pull = result2
                    return result

    def __init__(
        self,
        r1: Proposals[T_co],
        r2: Callable[[], Awaitable[Proposals[T_co]]],
        cutoff: float | None = None,
    ) -> None:
        self._state: Proposals[T_co] = StagedRollout.YieldUntil(
            active=r1, waiting=r2, cutoff=cutoff, parent=self
        )

    @override
    async def next(self, min_logprob: float = NEG_INF) -> Proposals.Approx[T_co]:
        return await self._state.next(min_logprob=min_logprob)


class Delay[Action](Proposals[Action]):
    """A `Rollout` that delays until it is asked to get at least a given approximation depth."""

    def __init__(self, wait: float, base: Callable[[], Proposals[Action]]) -> None:
        self._wait: float | None = wait
        self._base: Callable[[], Proposals[Action]] | Proposals[Action] = base

    @override
    async def next(self, min_logprob: float = NEG_INF) -> Proposals.Approx[Action]:
        if self._wait is None:
            assert isinstance(self._base, Proposals)
            return await self._base.next(min_logprob=min_logprob)
        if min_logprob < self._wait:
            self._wait = None
            assert not isinstance(self._base, Proposals)
            self._base = self._base()
            return await self._base.next(min_logprob=min_logprob)
        return Proposals.Approx(logprob=self._wait, result=None)


class DeduplicateRollout[T_co](Proposals[T_co]):
    def __init__(
        self,
        rollout: Proposals[T_co],
        *,
        compare: Callable[[T_co, T_co], bool] = lambda x, y: x is y,
    ) -> None:
        super().__init__()
        self._base = rollout
        self._seen: list[T_co] = []
        self._compare = compare

    def _add(self, candidate: T_co) -> bool:
        if any(self._compare(x, candidate) for x in self._seen):
            return False
        self._seen.append(candidate)
        return True

    @override
    async def next(self, min_logprob: float = NEG_INF) -> Proposals.Approx[T_co]:
        while True:
            proposal = await self._base.next(min_logprob=min_logprob)
            if proposal.result is None:
                return proposal
            if self._add(proposal.result):
                return proposal
            # we already returned this proposal, so we try to get the next one

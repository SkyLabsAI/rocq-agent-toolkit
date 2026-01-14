from __future__ import annotations

import heapq
from abc import ABC, abstractmethod
from collections.abc import Callable, Iterable, Iterator, Mapping, MutableMapping
from typing import Annotated, Any, TypeVar, override

from provenance_toolkit import Provenance

from .action import Action

T_co = TypeVar("T_co", covariant=True)


class Strategy[T_co](Provenance.Full, ABC):
    """Interface: producer of ranked _alternative_ `Action`s.

    A `Strategy` proposes `Action`s to take. The different proposals
    can be lazily drawn from a `Rollout` which allows capturing very
    large (even infinite) action spaces such as next tactic prediction
    in theorem proving.

    cf. ./action.py#Action
    """

    type Rollout[U] = Iterator[tuple[float, Action[U]]]
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
    """

    type Context = Mapping[str, Any]
    """Read-only context information that may be supplied during `Strategy.rollout`.

    Clients need not supply any `context: Context` but may choose to do so, e.g.
    to capture problem-level information such as the task description, or feedback
    from a previous attempt.
    """

    type MutableContext = MutableMapping[str, Any]
    """Mutable `Context`; useful for clients but unused by `Strategy`.

    `Strategy` uniformly uses `Context` and may not modify it during `rollout`.

    Clients may need to use `MutableContext` if they are incrementally building the
    initial context via cooperative inheritance, i.e.:
    ```python
    class Base:
        def prepare(...) -> MutableContext:
            ...

    class Derived(Base):
        @override
        def prepare(...) -> MutableContext:
            mut_ctx = super().prepare(...)
            ...
            return mut_ctx
    ```
    """

    @staticmethod
    def empty_Rollout() -> Strategy.Rollout:
        """The empty `Rollout` containing no `Action`s.

        If a `Strategy` does not apply it can return `empty_Rollout`.
        """
        yield from ()

    @abstractmethod
    def rollout(
        self,
        state: T_co,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[T_co]:
        """Build `Rollout` of ranked _alternative_ `Action`s for `state`.

        Given `state` and optional `context`, generate a `Rollout` containing no more
        than `max_rollout` ranked _alternative_ `Action`s. If `max_rollout`
        is `None` then `rollout` is unbounded (i.e. it may be infinite).

        Notes:
        - If a strategy does not apply, it should produce an empty generator.


        Arguments:
          - state: current state to get action alternatives for
          - max_rollout: maximum size of returned `Rollout`; None = no limit
          - context (optional): strategy specific, read-only context

        Returns: the `Rollout` of ranked _alternative_ `Action`s for `state`
        """
        pass


# Note: backwards-compatible symbol; we could remove this if we want.
empty_Rollout = Strategy.empty_Rollout


class SingletonStrategy[T_co](Strategy[T_co]):
    """
    A strategy that always returns a single action
    """

    _value: Annotated[Action[T_co], Provenance.Reflect.Field]
    _prob: Annotated[float, Provenance.Reflect.Field]

    def __init__(self, value: Action[T_co], prob: float = 1.0) -> None:
        self._value = value
        self._prob = prob

    def rollout(
        self,
        state: T_co,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout[T_co]:
        return iter([(self._prob, self._value)])


class IteratorStrategy[T_co](Strategy[T_co]):
    _collection: Annotated[
        Iterable[tuple[float, Action[T_co]]],
        Provenance.Reflect.Field,
    ]

    def __init__(self, i: Iterable[tuple[float, Action[T_co]]]) -> None:
        self._collection = i

    def rollout(
        self,
        state: T_co,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout[T_co]:
        return iter(self._collection)


class CompositeStrategy[T_co](Strategy[T_co]):
    """Combinator: fair interleaving of strategies.

    Each strategy will be asked for its `next` action, and the results
    will be interleaved according to their scores.

    For example, with two strategies that propose:
        - [(-0.5, act1), (-0.75, act2)]
        - [(-0.25, act3), (-0.35, act4)]
    will result in
        - [(-0.25, act3), (-0.35, act4), (-0.5, act1), (-0.75, act2)]

    The results  of an individual `Strategy` will not be re-ordered
    so the resulting list may be out-of-order if one of the passed
    `Strategy`s yields results out of order.
    """

    _children: Annotated[list[Strategy[T_co]], Provenance.Reflect.Field]

    def __init__(self, children: list[Strategy[T_co]]) -> None:
        self._children: list[Strategy[T_co]] = children

    @override
    def rollout(
        self,
        state: T_co,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout[T_co]:
        def combine() -> Strategy.Rollout[T_co]:
            queue: list[tuple[float, int, Action[T_co], Strategy.Rollout]] = []

            def push_next(i: int, g: Strategy.Rollout[T_co]) -> None:
                nonlocal queue
                try:
                    pr, act = next(g)
                except StopIteration:
                    return
                heapq.heappush(queue, (-pr, i, act, g))

            for i, strat in enumerate(self._children):
                gen = strat.rollout(state, max_rollout=max_rollout, context=context)
                push_next(i, gen)

            while True:
                try:
                    (pr, i, act, gen) = heapq.heappop(queue)
                except IndexError:
                    return
                yield (-pr, act)
                push_next(i, gen)

        return combine()


class StagedStrategy[T_co](Strategy[T_co]):
    """Combinator: biased interleaving of two strategies, preferring the first.

    All results from `strat1` that are greater than or equal to `prob` will
    be returned before `strat2` is considered, at which point results from
    `strat1` and `strat2` will be interleaved as they are in `CompositeStrategy`.
    """

    _strat1: Annotated[Strategy[T_co], Provenance.Reflect.Field]
    _strat2: Annotated[Strategy[T_co], Provenance.Reflect.Field]
    _prob: Annotated[float | None, Provenance.Reflect.Field]

    def __init__(
        self, strat1: Strategy[T_co], strat2: Strategy[T_co], prob: float | None = None
    ) -> None:
        """
        If `prob = None`, then `strat1` will be entirely consumed before
        `strat2` is invoked.
        """
        self._strat1 = strat1
        self._strat2 = strat2
        self._prob = prob
        super().__init__()

    def rollout(
        self,
        state: T_co,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout[T_co]:
        def combine2(
            r1: Strategy.Rollout[T_co],
            pr2: float,
            act2: Action[T_co],
            r2: Strategy.Rollout[T_co],
        ) -> Strategy.Rollout[T_co]:
            try:
                pr1, act1 = next(r1)
            except StopIteration:
                yield (pr2, act2)
                yield from r2
                return
            if pr2 <= pr1:
                yield (pr1, act1)
                yield from combine2(r1, pr2, act2, r2)
            else:
                yield (pr2, act2)
                yield from combine2(r2, pr1, act1, r1)

        def combine(r: Strategy.Rollout[T_co]) -> Strategy.Rollout[T_co]:
            while True:
                try:
                    pr, result = next(r)
                except StopIteration:
                    yield from self._strat2.rollout(state, max_rollout, context)
                    return

                if self._prob is None or pr >= self._prob:
                    yield (pr, result)
                else:
                    yield from combine2(
                        self._strat2.rollout(state, max_rollout, context),
                        pr,
                        result,
                        r,
                    )
                    return

        return combine(self._strat1.rollout(state, max_rollout, context))


def staged[T](strats: list[tuple[float | None, Strategy[T]]]) -> Strategy[T]:
    """
    Build an iterated StagedStrategy.
    If the element `(pr,strat)` exists in the list, then `strat` will start
    being considered once prior strategies yield a probability less than `pr`.
    """
    if not strats:
        return FailStrategy()
    last_prob, current = strats[-1]
    for prob, s in reversed(strats[:-1]):
        current = StagedStrategy(s, current, last_prob)
        last_prob = prob
    return current


class FailStrategy[T_co](Strategy[T_co]):
    """A simple strategy that fails."""

    @override
    def rollout(
        self,
        state: T_co,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout:
        return empty_Rollout()


class GuardStrategy[T_co, With](FailStrategy[T_co]):
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
    ) -> Strategy.Rollout: ...

    @override
    def rollout(
        self,
        state: T_co,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout:
        val = self.check(state)
        if val is None:
            return super().rollout(state, max_rollout, context)
        return self.rollout_with(val, state, max_rollout, context)


class WrapAction[T, U](Action[T]):
    """A wrapper for Actions based on lenses.

    Converts an `Action[U]` to an `Action[T]` given functions
    - `into: Callable[[T],U]`
    - `outof: Callable[[T, U], T]` -- the first argument is the original
      state. This function should return a **new** value of type `T`, it
      should **not** mutate the original value.

    Note: Since `Action` is a effectively where its argument occurs
    both positively and negatively, we need both `into` and `outof`.
    """

    _base: Annotated[Action[U], Provenance.Reflect.Field]
    _into: Annotated[Callable[[T], U], Provenance.Reflect.CallableField]
    _outof: Annotated[Callable[[T, U], T], Provenance.Reflect.CallableField]

    def __init__(
        self, base: Action[U], into: Callable[[T], U], outof: Callable[[T, U], T]
    ) -> None:
        self._base = base
        self._into = into
        self._outof = outof

    @override
    def interact(self, state: T) -> T:
        return self._outof(state, self._base.interact(self._into(state)))


class WrapStrategy[T, U](Strategy[T]):
    """A wrapper of `Strategy` based on lenses.

    See the documentation for `WrapAction`.
    """

    _base: Annotated[Strategy[U], Provenance.Reflect.Field]
    _into: Annotated[Callable[[T], U], Provenance.Reflect.CallableField]
    _outof: Annotated[Callable[[T, U, Action[U]], T], Provenance.Reflect.CallableField]

    def __init__(
        self,
        base: Strategy[U],
        into: Callable[[T], U],
        outof: Callable[[T, U, Action[U]], T],
    ) -> None:
        self._base = base
        self._into = into
        self._outof = outof

    @override
    def rollout(
        self,
        state: T,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout:
        outof = self._outof

        def mk(action: Action[U]) -> Action[T]:
            nonlocal outof
            return WrapAction(action, self._into, lambda a, b: outof(a, b, action))

        return (
            (prob, mk(action))
            for prob, action in self._base.rollout(
                self._into(state), max_rollout=max_rollout, context=context
            )
        )

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Callable, Iterable, Mapping, MutableMapping, Sequence
from typing import Annotated, Any, TypeVar, override

from provenance_toolkit import Provenance

from .rollout import (
    ApproximatingRollout,
    EmptyRollout,
    InterleaveRollout,
    MapRollout,
    Rollout,
    StagedRollout,
    singleton,
)

T_co = TypeVar("T_co", covariant=True)


class Strategy[State, Action](Provenance.Full, ABC):
    """Interface: producer of ranked _alternative_ `Action`s.

    A `Strategy` proposes `Action`s to take. The different proposals
    can be lazily drawn from a `Rollout` which allows capturing very
    large (even infinite) action spaces such as next tactic prediction
    in theorem proving.

    cf. ./action.py#Action
    """

    # Context information must be read-only and constant in order
    # for searches to work correctly. Clients should use an
    # implementation such as `immutabledict` to achieve this.
    # Mutable information needs to be tracked in the state
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

    @abstractmethod
    async def rollout(
        self,
        state: State,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action]:
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


class SingletonStrategy[State, Action](Strategy[State, Action]):
    """
    A strategy that always returns a single action
    """

    _value: Annotated[Action, Provenance.Reflect.Field]
    _prob: Annotated[float, Provenance.Reflect.Field]

    def __init__(self, value: Action, logprob: float = 1.0) -> None:
        self._value = value
        self._logprob = logprob

    @override
    async def rollout(
        self,
        state: State,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action]:
        return singleton(self._value, score=self._logprob)


class IteratorStrategy[State, Action](Strategy[State, Action]):
    _collection: Annotated[
        Iterable[tuple[float, Action]],
        Provenance.Reflect.Field,
    ]

    def __init__(self, i: Iterable[tuple[float, Action]]) -> None:
        self._collection = i

    @override
    async def rollout(
        self,
        state: State,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action]:
        return ApproximatingRollout(
            (
                Rollout.Approx(logprob=logprob, result=act)
                for logprob, act in self._collection
            )
        )


class CompositeStrategy[State, Action](Strategy[State, Action]):
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

    _children: Annotated[Sequence[Strategy[State, Action]], Provenance.Reflect.Field]

    def __init__(self, children: Sequence[Strategy[State, Action]]) -> None:
        self._children = children

    @override
    async def rollout(
        self,
        state: State,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action]:
        return InterleaveRollout(
            [
                await strat.rollout(state, max_rollout, context=context)
                for strat in self._children
            ]
        )


def composite[T, Act](*strats: Strategy[T, Act]) -> Strategy[T, Act]:
    return CompositeStrategy(strats)


class StagedStrategy[State, Action](Strategy[State, Action]):
    """Combinator: biased interleaving of two strategies, preferring the first.

    All results from `strat1` that are greater than or equal to `prob` will
    be returned before `strat2` is considered, at which point results from
    `strat1` and `strat2` will be interleaved as they are in `CompositeStrategy`.
    """

    _strat1: Annotated[Strategy[State, Action], Provenance.Reflect.Field]
    _strat2: Annotated[Strategy[State, Action], Provenance.Reflect.Field]
    _prob: Annotated[float | None, Provenance.Reflect.Field]

    def __init__(
        self,
        strat1: Strategy[State, Action],
        strat2: Strategy[State, Action],
        prob: float | None = None,
    ) -> None:
        """
        If `prob = None`, then `strat1` will be entirely consumed before
        `strat2` is invoked.
        """
        self._strat1 = strat1
        self._strat2 = strat2
        self._prob = prob
        super().__init__()

    @override
    async def rollout(
        self,
        state: State,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action]:
        async def fn():
            return await self._strat2.rollout(
                state, max_rollout=max_rollout, context=context
            )

        return StagedRollout(
            await self._strat1.rollout(state, max_rollout=max_rollout, context=context),
            fn,
            self._prob,
        )


def staged[State, Action](
    strats: list[tuple[float | None, Strategy[State, Action]]],
) -> Strategy[State, Action]:
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


class FailStrategy[State, Action](Strategy[State, Action]):
    """A simple strategy that fails."""

    @override
    def rollout(
        self,
        state: State,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action]:
        return EmptyRollout()


class GuardStrategy[State, With, Action](FailStrategy[State, Action], ABC):
    """Guard the execution of a strategy.
    If [check] returns [None], then this strategy acts like the [FailStrategy] otherwise
    it does [rollout_with]
    """

    @abstractmethod
    def check(
        self, state: State, context: Strategy.Context | None = None
    ) -> With | None: ...

    @abstractmethod
    def rollout_with(
        self,
        val: With,
        rdm: State,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action]: ...

    @override
    def rollout(
        self,
        state: State,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[Action]:
        val = self.check(state)
        if val is None:
            return super().rollout(state, max_rollout, context)
        return self.rollout_with(val, state, max_rollout, context)


class MapStategy[T, T_act, U, U_act](Strategy[T, T_act]):
    """A wrapper of `Strategy` based on lenses.

    See the documentation for `WrapAction`.
    """

    _base: Annotated[Strategy[U, U_act], Provenance.Reflect.Field]
    _fn_state: Annotated[Callable[[T], U], Provenance.Reflect.CallableField]
    _fn: Annotated[Callable[[T, U, U_act], T_act], Provenance.Reflect.CallableField]

    def __init__(
        self,
        base: Strategy[U, U_act],
        fn_state: Callable[[T], U],
        fn_action: Callable[[T, U, U_act], T_act],
    ) -> None:
        self._base = base
        self._fn_state = fn_state
        self._fn_action = fn_action

    @override
    def rollout(
        self,
        state: T,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout[T_act]:
        u_state = self._fn_state(state)
        fn = self._fn_action
        return MapRollout(
            self._base.rollout(u_state, max_rollout, context),
            lambda act: fn(state, u_state, act),
        )


#
# Strategy repetition is a bit subtle because it implicitly
# assumes some randomization and tries to implement that
# generically on top of an arbitrary randomized program.
#
# There are two ways to implement **parametric** repetition with
# different properties.
# 1. Propose all of the options from the strategy once and then
#    duplicate them.
# 2. Get all of the proposals from the repetitions and then
#    interleave them.
# The former will (almost always) produce un-sorted proposals
# but it will also ensure to try the greatest variation in
# proposals.
# By contrast, the later will produce sorted proposals
# (assuming the underlying strategies produce sorted proposals)
# which may hide the low-score proposals.
#
# Non-parametric Repetition
# ==========================
# An alternative to strategy repetition is to implement repetition
# within the strategy itself, e.g. by prompting an LLM to "return 5
# proposals" rather than prompting it to return 1 proposal five times.
#


def repeat[State, Action](
    strategy: Strategy[State, Action], repeat: int
) -> Strategy[State, Action]:
    """
    Repeat a base strategy to get multiple candidates per node.
    So all the elements of the strategy are tried
    the first time, and then again subsequent times.

    This is intendend to be used with non-deterministic strategies.

    If the underlying Strategy returns `[a_n,b_n,c_n]`, then
    `repeat(base, 3)` will return `[a_1,b_1,c_1,a_2,b_2,c_2,a_3,b_3,c_3]`.

    NOTE: This Strategy violates the convention that scores arrive
    in decreasing order if the underlying strategy returns
    multiple actions with different probabilities.
    """
    return staged([(None, strategy)] * repeat)


def self_interleave[State, Action](
    strategy: Strategy[State, Action], repeat: int
) -> Strategy[State, Action]:
    """Interleaves the strategy with itself repeat times"""
    return CompositeStrategy([strategy] * repeat)

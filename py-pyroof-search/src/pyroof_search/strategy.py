from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import (
    Awaitable,
    Callable,
    Iterable,
    Mapping,
    MutableMapping,
    Sequence,
)
from typing import Annotated, Any, TypeVar, override

from provenance_toolkit import Provenance

from . import rollout as ProposalsL  # ProposalsLibrary
from .rollout import (
    ApproximatingProposals,
    AsyncMapRollout,
    EmptyProposals,
    InterleaveRollout,
    Proposals,
    StagedRollout,
)

T_co = TypeVar("T_co", covariant=True)


class Proposer[State, Action](Provenance.Full, ABC):
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
        context: Proposer.Context | None = None,
    ) -> Proposals[Action]:
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


class SingletonProposer[State, Action](Proposer[State, Action]):
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
        context: Proposer.Context | None = None,
    ) -> Proposals[Action]:
        return ProposalsL.singleton(self._value, score=self._logprob)


class IteratorProposer[State, Action](Proposer[State, Action]):
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
        context: Proposer.Context | None = None,
    ) -> Proposals[Action]:
        return ApproximatingProposals(
            (
                Proposals.Approx(logprob=logprob, result=act)
                for logprob, act in self._collection
            )
        )


class CompositeProposer[State, Action](Proposer[State, Action]):
    """Combinator: fair interleaving of Proposers.

    Each Proposer will be asked for its `next` action, and the results
    will be interleaved according to their scores.

    For example, with two strategies that propose:
        - [(-0.5, act1), (-0.75, act2)]
        - [(-0.25, act3), (-0.35, act4)]
    will result in
        - [(-0.25, act3), (-0.35, act4), (-0.5, act1), (-0.75, act2)]

    The results  of an individual `Proposer` will not be re-ordered
    so the resulting list may be out-of-order if one of the passed
    `Proposer`s yields results out of order.
    """

    _children: Annotated[Sequence[Proposer[State, Action]], Provenance.Reflect.Field]

    def __init__(self, children: Sequence[Proposer[State, Action]]) -> None:
        self._children = children

    @override
    async def rollout(
        self,
        state: State,
        max_rollout: int | None = None,
        context: Proposer.Context | None = None,
    ) -> Proposals[Action]:
        return InterleaveRollout(
            [
                await strat.rollout(state, max_rollout, context=context)
                for strat in self._children
            ]
        )


def composite[T, Act](*strats: Proposer[T, Act]) -> Proposer[T, Act]:
    return CompositeProposer(strats)


class StagedProposer[State, Action](Proposer[State, Action]):
    """Combinator: biased interleaving of two strategies, preferring the first.

    All results from `strat1` that are greater than or equal to `prob` will
    be returned before `strat2` is considered, at which point results from
    `strat1` and `strat2` will be interleaved as they are in `CompositeStrategy`.
    """

    _strat1: Annotated[Proposer[State, Action], Provenance.Reflect.Field]
    _strat2: Annotated[Proposer[State, Action], Provenance.Reflect.Field]
    _prob: Annotated[float | None, Provenance.Reflect.Field]

    def __init__(
        self,
        strat1: Proposer[State, Action],
        strat2: Proposer[State, Action],
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
        context: Proposer.Context | None = None,
    ) -> Proposals[Action]:
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
    strats: list[tuple[float | None, Proposer[State, Action]]],
) -> Proposer[State, Action]:
    """
    Build an iterated StagedStrategy.
    If the element `(pr,strat)` exists in the list, then `strat` will start
    being considered once prior strategies yield a probability less than `pr`.
    """
    if not strats:
        return FailProposer()
    last_prob, current = strats[-1]
    for prob, s in reversed(strats[:-1]):
        current = StagedProposer(s, current, last_prob)
        last_prob = prob
    return current


class FailProposer[State, Action](Proposer[State, Action]):
    """A simple strategy that fails."""

    @override
    async def rollout(
        self,
        state: State,
        max_rollout: int | None = None,
        context: Proposer.Context | None = None,
    ) -> Proposals[Action]:
        return EmptyProposals()


class GuardProposer[State, With, Action](FailProposer[State, Action], ABC):
    """Guard the execution of a strategy.
    If [check] returns [None], then this strategy acts like the [FailStrategy] otherwise
    it does [rollout_with]
    """

    @abstractmethod
    async def check(
        self, state: State, context: Proposer.Context | None = None
    ) -> With | None: ...

    @abstractmethod
    async def rollout_with(
        self,
        val: With,
        rdm: State,
        max_rollout: int | None = None,
        context: Proposer.Context | None = None,
    ) -> Proposals[Action]: ...

    @override
    async def rollout(
        self,
        state: State,
        max_rollout: int | None = None,
        context: Proposer.Context | None = None,
    ) -> Proposals[Action]:
        val = await self.check(state)
        if val is None:
            return await super().rollout(state, max_rollout, context)
        return await self.rollout_with(val, state, max_rollout, context)


class MapProposer[T, T_act, U, U_act](Proposer[T, T_act]):
    """A wrapper of `Proposer` based on lenses.

    See the documentation for `WrapAction`.
    """

    _base: Annotated[Proposer[U, U_act], Provenance.Reflect.Field]
    _into: Annotated[Callable[[T], U], Provenance.Reflect.CallableField]
    _outof: Annotated[Callable[[T, U, U_act], T_act], Provenance.Reflect.CallableField]

    def __init__(
        self,
        base: Proposer[U, U_act],
        *,
        into: Callable[[T], U],
        outof: Callable[[T, U, U_act], T_act],
    ) -> None:
        self._base = base
        self._into = into
        self._fn_action = outof

    @override
    async def rollout(
        self,
        state: T,
        max_rollout: int | None = None,
        context: Proposer.Context | None = None,
    ) -> Proposals[T_act]:
        u_state = self._into(state)

        def fn(act: U_act) -> T_act:
            return self._fn_action(state, u_state, act)

        return ProposalsL.map(
            await self._base.rollout(u_state, max_rollout, context),
            fn,
        )


class AsyncMapProposer[T, T_act, U, U_act](Proposer[T, T_act]):
    """A wrapper of `Strategy` based on lenses.

    See the documentation for `AsyncWrapAction`.
    """

    _base: Annotated[Proposer[U, U_act], Provenance.Reflect.Field]
    _into: Annotated[Callable[[T], Awaitable[U]], Provenance.Reflect.CallableField]
    _outof: Annotated[
        Callable[[T, U, U_act], Awaitable[T_act]], Provenance.Reflect.CallableField
    ]

    def __init__(
        self,
        base: Proposer[U, U_act],
        *,
        into: Callable[[T], Awaitable[U]],
        outof: Callable[[T, U, U_act], Awaitable[T_act]],
    ) -> None:
        self._base = base
        self._into = into
        self._fn_action = outof

    @override
    async def rollout(
        self,
        state: T,
        max_rollout: int | None = None,
        context: Proposer.Context | None = None,
    ) -> Proposals[T_act]:
        u_state = await self._into(state)

        async def fn(act: U_act) -> T_act:
            return await self._fn_action(state, u_state, act)

        return AsyncMapRollout(
            await self._base.rollout(u_state, max_rollout, context),
            fn,
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
    proposer: Proposer[State, Action], repeat: int
) -> Proposer[State, Action]:
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
    return staged([(None, proposer)] * repeat)


def self_interleave[State, Action](
    proposer: Proposer[State, Action], repeat: int
) -> Proposer[State, Action]:
    """Interleaves the strategy with itself repeat times"""
    return CompositeProposer([proposer] * repeat)

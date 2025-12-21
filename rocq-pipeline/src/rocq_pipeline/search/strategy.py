from __future__ import annotations

import heapq
from abc import ABC, abstractmethod
from collections.abc import Generator, Mapping
from typing import Any, override

from rocq_doc_manager import RocqCursor


class Action[T]:
    """
    An `Action` represents a (potential) action in an MDP.

    They support failure in order to support instances
    where no action exists. Mathematically, failed actions
    could be modeled by enriching the MDP with a unique
    failure state, but explicitly communicating this
    avoids the need to modify the MDP.
    """

    @abstractmethod
    def interact(self, rc: T) -> bool:
        return False


class TacticAction(Action[RocqCursor]):
    def __init__(self, tactic: str) -> None:
        self._tactic = tactic

    @override
    def interact(self, rc: RocqCursor) -> bool:
        response = self.run_tactic(rc, self._tactic)
        return not issubclass(type(response), RocqCursor.Err)

    def run_tactic(
        self, rc: RocqCursor, tactic: str
    ) -> RocqCursor.CommandData | RocqCursor.Err[RocqCursor.CommandError]:
        return rc.insert_command(tactic)


class Strategy(ABC):
    """
    A `Strategy` proposes actions to take. The different proposals
    are captured lazily using a `Generator`. This allows capturing
    very large (even infinite) action spaces such as next tactic
    prediction in theorem proving.
    """

    type Action = Action[RocqCursor]
    # TODO: make [Rollout] into a class
    type Rollout = Generator[tuple[float, Strategy.Action]]

    # Context information must be read-only and constant in order
    # for searches to work correctly. Clients should use an
    # implementation such as `immutabledict` to achieve this.
    # Mutable information needs to be tracked in the state
    type Context = Mapping[str, Any]

    @abstractmethod
    def rollout(
        self,
        rdm: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Rollout:
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


class CompositeStrategy(Strategy):
    """A (fair) combination of strategies"""

    def __init__(self, children: list[Strategy]) -> None:
        self._children: list[Strategy] = children

    @override
    def rollout(
        self,
        rdm: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout:
        def combine() -> Strategy.Rollout:
            queue: list[tuple[float, int, Strategy.Action, Strategy.Rollout]] = []
            for i, strat in enumerate(self._children):
                gen = strat.rollout(rdm, max_rollout=max_rollout)
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


class SafeTacticStrategy(Strategy):
    """A simple strategy that always returns a tactic."""

    def __init__(self, tactic: str, prob: float = 1.0) -> None:
        self._tactic: str = tactic
        self._prob: float = prob

    @override
    def rollout(
        self,
        rdm: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout:
        return (
            (prob, TacticAction(f"progress {tac}"))
            for prob, tac in [(self._prob, self._tactic)]
        )


class CutAssertStrategy(Strategy):
    """A simple strategy that cuts a Rocq lemma.
    The success probability 1.0 is not necessarily appropriate."""

    def __init__(self, name: str, lemma: str, prob: float = 1.0) -> None:
        self._name: str = name
        self._lemma: str = lemma
        self._prob: float = prob

    @override
    def rollout(
        self,
        rdm: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout:
        name: str | RocqCursor.Err[None] = rdm.fresh_ident(self._name)
        if isinstance(name, RocqCursor.Err):
            return empty_Rollout()

        # For now, it is important that we fail if this fact is already known,
        # otherwise we risk looping here
        tac: str = f"assert ({self._lemma}) as {name}; [ assert_fails tauto | ]"

        return ((prob, TacticAction(t)) for prob, t in [(self._prob, tac)])


class FailStrategy(Strategy):
    """A simple strategy that fails."""

    @override
    def rollout(
        self,
        rdm: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout:
        return empty_Rollout()


class FirstTacticStrategy(Strategy):
    """A simple strategy that tries each of the given tactics with their given probabilities."""

    def __init__(self, tactics: list[tuple[float, str | Action]]) -> None:
        def mk(x: str | Action) -> Action:
            if isinstance(x, Action):
                return x
            return TacticAction(x)

        self._tactics: list[tuple[float, Action]] = [
            (prob, mk(tac)) for prob, tac in sorted(tactics, reverse=True)
        ]

    @override
    def rollout(
        self,
        rdm: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout:
        return ((prob, tac) for prob, tac in self._tactics)


class GuardStrategy[T](FailStrategy, ABC):
    """Guard the execution of a strategy.
    If [check] returns [None], then this strategy acts like the [FailStrategy] otherwise
    it does [rollout_with]
    """

    @abstractmethod
    def check(
        self, rdm: RocqCursor, context: Strategy.Context | None = None
    ) -> T | None: ...

    @abstractmethod
    def rollout_with(
        self,
        val: T,
        rdm: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout: ...

    @override
    def rollout(
        self,
        rdm: RocqCursor,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout:
        val = self.check(rdm)
        if val is None:
            return super().rollout(rdm, max_rollout, context)
        return self.rollout_with(val, rdm, max_rollout, context)

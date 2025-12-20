from __future__ import annotations

import heapq
import itertools
from abc import ABC, abstractmethod
from collections.abc import Generator
from typing import override

from rocq_doc_manager import RocqCursor


class Action[T]:
    """
    Actions capture interactions with documents.
    In most cases, an action will result in a single interaction, e.g. applying a tactic;
    however, more flexibility is provided in order to allow for successive queries to the
    document or applying multiple tactics.
    """

    class FailedAction(Exception):
        pass

    @abstractmethod
    def step(self, rc: T) -> T:
        """
        Advance to a new state returning the new state.

        Raises `FailedAction` if the step does not apply
        """
        raise Action.FailedAction()


class RocqTacticAction(Action[RocqCursor]):
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


def interleave[T](ls: list[Generator[T]]) -> Generator[T]:
    """Interleave all the values from the generator in a fair manner"""
    gens: list[tuple[T, int, Generator[T]]] = []

    def pull(g: Generator[T], fresh: int) -> None:
        nonlocal gens
        try:
            n = next(g)
            heapq.heappush(gens, (n, fresh, g))
        except StopIteration:
            pass

    for i, g in enumerate(ls):
        pull(g, fresh=i)

    while gens:
        v, i, rest = heapq.heappop(gens)
        yield v
        pull(rest, fresh=i)


class Rollout[T]:
    def logprob(self) -> float:
        """
        The returned value is an approximation of the probability of the next action being good
        """
        return 0.0

    def next(self, prob_min: float = -float("inf")) -> T:
        """
        Get the next action.
        `prob_min` is the cutoff, the rollout knows that it won't produce a guess better than
        `prob_min`, then it can delay by returning `None`.

        Raises `StopIteration` when there are no items left.
        """
        raise StopIteration


class Strategy[T](ABC):
    """
    A `Strategy` proposes actions to take
    """

    # TODO: make [Rollout] into a class
    # type Rollout[U] = Generator[tuple[float, Action[U]]]

    @abstractmethod
    def rollout(self, cursor: T, max_rollout: int | None = None) -> Rollout[Action[T]]:
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


def empty_Rollout[T]() -> Strategy.Rollout[T]:
    yield from ()


class CompositeStrategy[T](Strategy[T]):
    """A (fair) combination of strategies"""

    def __init__(self, children: list[Strategy[T]]) -> None:
        self._children: list[Strategy[T]] = children

    @override
    def rollout(self, rdm: T, max_rollout: int | None = None) -> Strategy.Rollout[T]:
        return interleave(
            [strat.rollout(rdm, max_rollout=max_rollout) for strat in self._children]
        )


class SafeTacticStrategy(Strategy[RocqCursor]):
    """A simple strategy that always returns a tactic."""

    def __init__(self, tactic: str, prob: float = 1.0) -> None:
        self._tactic: str = tactic
        self._prob: float = prob

    @override
    def rollout(
        self, rdm: RocqCursor, max_rollout: int | None = None
    ) -> Strategy.Rollout:
        return (
            (prob, RocqTacticAction(f"progress {tac}"))
            for prob, tac in [(self._prob, self._tactic)]
        )


class CutAssertStrategy(Strategy[RocqCursor]):
    """A simple strategy that cuts a Rocq lemma.
    The success probability 1.0 is not necessarily appropriate."""

    def __init__(self, name: str, lemma: str, prob: float = 1.0) -> None:
        self._name: str = name
        self._lemma: str = lemma
        self._prob: float = prob

    @override
    def rollout(
        self, rdm: RocqCursor, max_rollout: int | None = None
    ) -> Strategy.Rollout:
        name: str | RocqCursor.Err[None] = rdm.fresh_ident(self._name)
        if isinstance(name, RocqCursor.Err):
            return empty_Rollout()

        # For now, it is important that we fail if this fact is already known,
        # otherwise we risk looping here
        tac: str = f"assert ({self._lemma}) as {name}; [ assert_fails tauto | ]"

        return ((prob, RocqTacticAction(t)) for prob, t in [(self._prob, tac)])


class FailStrategy[T](Strategy[T]):
    """A simple strategy that fails."""

    @override
    def rollout(self, rdm: T, max_rollout: int | None = None) -> Strategy.Rollout[T]:
        return empty_Rollout()


class FirstTacticStrategy(Strategy[RocqCursor]):
    """A simple strategy that tries each of the given tactics with their given probabilities."""

    def __init__(self, tactics: list[tuple[float, str | Action]]) -> None:
        def mk(x: str | Action) -> Action:
            if isinstance(x, Action):
                return x
            return RocqTacticAction(x)

        self._tactics: list[tuple[float, Action]] = [
            (prob, mk(tac)) for prob, tac in sorted(tactics, reverse=True)
        ]

    @override
    def rollout(
        self, rdm: RocqCursor, max_rollout: int | None = None
    ) -> Strategy.Rollout:
        return ((prob, tac) for prob, tac in self._tactics)


class GuardStrategy[T](FailStrategy[T], ABC):
    """Guard the execution of a strategy.
    If [check] returns [None], then this strategy acts like the [FailStrategy] otherwise
    it does [rollout_with]
    """

    @abstractmethod
    def check(self, rdm: T) -> T | None: ...

    @abstractmethod
    def rollout_with(
        self, val: T, rdm: T, max_rollout: int | None = None
    ) -> Strategy.Rollout[T]: ...

    @override
    def rollout(self, rdm: T, max_rollout: int | None = None) -> Strategy.Rollout[T]:
        val = self.check(rdm)
        if val is None:
            return super().rollout(rdm, max_rollout)
        return self.rollout_with(val, rdm, max_rollout)

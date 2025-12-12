import heapq
from abc import ABC, abstractmethod
from collections.abc import Generator
from typing import override

from rocq_doc_manager import RocqCursor

from rocq_pipeline.agent.base import TacticApplication


class Strategy(ABC):
    """
    A `Strategy` proposes actions to take
    """

    type Action = TacticApplication
    # TODO: make [Rollout] into a class
    type Rollout = Generator[tuple[float, Action]]

    @abstractmethod
    def rollout(self, rdm: RocqCursor, max_rollout: int | None = None) -> Rollout:
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
        self, rdm: RocqCursor, max_rollout: int | None = None
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
                    (pr, i, act, gen) = queue.pop(0)
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
        self, rdm: RocqCursor, max_rollout: int | None = None
    ) -> Strategy.Rollout:
        return (
            (prob, TacticApplication(tac)) for prob, tac in [(self._prob, self._tactic)]
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
        self, rdm: RocqCursor, max_rollout: int | None = None
    ) -> Strategy.Rollout:
        name: str | RocqCursor.Err[None] = rdm.fresh_ident(self._name)
        if isinstance(name, RocqCursor.Err):
            return empty_Rollout()
        tac: str = f"assert ({self._lemma}) as {name}"

        return ((prob, TacticApplication(t)) for prob, t in [(self._prob, tac)])


class FailStrategy(Strategy):
    """A simple strategy that fails."""

    @override
    def rollout(
        self, rdm: RocqCursor, max_rollout: int | None = None
    ) -> Strategy.Rollout:
        return empty_Rollout()


class FirstTacticStrategy(Strategy):
    """A simple strategy that tries each of the given tactics with their given probabilities."""

    def __init__(self, tactics: list[tuple[float, str]]) -> None:
        self._tactics: list[tuple[float, str]] = sorted(tactics, reverse=True)

    @override
    def rollout(
        self, rdm: RocqCursor, max_rollout: int | None = None
    ) -> Strategy.Rollout:
        return ((prob, TacticApplication(tac)) for prob, tac in self._tactics)


class GuardStrategy[T](FailStrategy, ABC):
    """Guard the execution of a strategy.
    If [check] returns [None], then this strategy acts like the [FailStrategy] otherwise
    it does [rollout_with]
    """

    @abstractmethod
    def check(self, rdm: RocqCursor) -> T | None: ...

    @abstractmethod
    def rollout_with(
        self, val: T, rdm: RocqCursor, max_rollout: int | None = None
    ) -> Strategy.Rollout: ...

    @override
    def rollout(
        self, rdm: RocqCursor, max_rollout: int | None = None
    ) -> Strategy.Rollout:
        val = self.check(rdm)
        if val is None:
            return super().rollout(rdm, max_rollout)
        return self.rollout_with(val, rdm, max_rollout)


import heapq
from abc import ABC, abstractmethod
from collections.abc import Generator
from typing import override

from rocq_doc_manager import RocqDocManager

from rocq_pipeline.agent.base import TacticApplication


class Strategy(ABC):
    """
    A `Strategy` proposes actions to take
    """
    type Action = TacticApplication
    type Rollout = Generator[tuple[float, Action]]

    @abstractmethod
    def rollout(self, rdm: RocqDocManager) -> Rollout:
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

class CompositeStrategy(Strategy):
    """A (fair) combination of strategies"""
    def __init__(self, children:list[Strategy]) -> None:
        self._children = children

    @override
    def rollout(self, rdm: RocqDocManager) -> Strategy.Rollout:
        def combine() -> Strategy.Rollout:
            queue:list[tuple[float,int,Strategy.Action,Strategy.Rollout]] = []
            for i, strat in enumerate(self._children):
                gen = strat.rollout(rdm)
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
    def __init__(self, tactic: str, prob:float = 1.0) -> None:
        self._tactic = tactic
        self._prob = prob

    @override
    def rollout(self, rdm: RocqDocManager) -> Strategy.Rollout:
        return ((prob, TacticApplication(tac)) for prob, tac in [(self._prob, self._tactic)])

from abc import ABC, abstractmethod
from collections.abc import Callable
from typing import override

from rocq_doc_manager import RocqCursor


class Guidance[T, U](ABC):
    @abstractmethod
    def score(self, cursor: T, logprob: float | None = None) -> U:
        """The score of the node."""
        ...


class LLMGuidance(Guidance[RocqCursor, float]):
    @override
    def score(self, cursor: RocqCursor, logprob: float | None = None) -> float:
        return -float("inf")


class GoalBasedGuidance[U](Guidance[RocqCursor, U]):
    def __init__(
        self, guidance: Guidance[RocqCursor, U], combine: Callable[[list[U]], U] = min
    ) -> None:
        self._guidance = guidance
        self._combine = combine

    @override
    def score(self, cursor: RocqCursor, logprob: float | None = None) -> U:
        raise NotImplementedError()
        # return self.combine(
        #     [llm.score(goal) for goal in cursor.current_goal().subgoals]
        # )

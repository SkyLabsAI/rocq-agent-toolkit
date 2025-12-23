from __future__ import annotations

from abc import ABC, abstractmethod


class Guidance[T](ABC):
    """
    Guidance provides a heuristic score for states during search.
    Lower scores are better (closer to goal/solution).
    """

    @abstractmethod
    def score(self, state: T, logprob: float | None = None) -> float:
        """
        Score a state. Lower is better.

        Args:
            state: The state to score
            logprob: Optional log probability from the strategy (can be combined with heuristic)

        Returns:
            A score where lower values indicate better states
        """


class UniformGuidance[T](Guidance[T]):
    """Default guidance that treats all states equally (returns constant score)."""

    def score(self, state: T, logprob: float | None = None) -> float:
        # Use negative log probability if available, otherwise 0
        return -logprob if logprob is not None else 0.0

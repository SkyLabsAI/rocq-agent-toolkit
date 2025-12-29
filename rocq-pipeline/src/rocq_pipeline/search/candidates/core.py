"""Core abstractions for candidate generation."""

from __future__ import annotations

from collections.abc import Callable, Iterator
from dataclasses import dataclass
from typing import Protocol

from ..action import Action
from ..strategy import Strategy


@dataclass(frozen=True)
class Candidate:
    """
    A proposed action before execution.

    Candidates are domain-agnostic strings that can be converted to
    domain-specific Actions (e.g., Rocq tactics, Lean tactics, chess moves).
    """

    text: str
    """The candidate action as a string (e.g., "auto.", "e2e4")."""

    logprob: float = 0.0
    """
    Log probability from the generator.
    Higher (less negative) = more confident.
    """


class CandidateGenerator(Protocol):
    """
    Generate candidate actions from a state description.

    This is the integration point for LLM-based or heuristic candidate
    generation. Implementations live in application code.

    Examples:
        - LLM tactic generator for theorem proving
        - Move generator for games
        - Transform generator for puzzles
    """

    def generate(
        self,
        state_desc: str,
        *,
        limit: int | None = None,
    ) -> Iterator[Candidate]:
        """
        Generate candidates for the given state.

        Args:
            state_desc: String description of current state (goal, board, grid, etc.)
            limit: Maximum number of candidates to generate

        Yields:
            Candidates in descending probability order (best first)
        """
        ...


class CandidateRectifier(Protocol):
    """
    Rectify (correct) a failed candidate given error feedback.

    Implementations typically use LLMs to fix syntax errors or
    semantic issues based on error messages.
    """

    def rectify(
        self,
        state_desc: str,
        candidate: str,
        error: str,
    ) -> str | None:
        """
        Attempt to fix a failed candidate.

        Args:
            state_desc: String description of current state
            candidate: The candidate that failed
            error: Error message from the failure

        Returns:
            Rectified candidate string, or None if unfixable
        """
        ...


class GeneratorStrategy[StateT](Strategy[StateT]):
    """
    Strategy that uses a CandidateGenerator.

    Bridges Layer 3 (domain-agnostic candidate generation) to
    Layer 0 (domain-specific Strategy/Action execution).

    Example:
        >>> strategy = GeneratorStrategy(
        ...     generator=my_llm_generator,
        ...     get_state_desc=lambda cursor: cursor.current_goal(),
        ...     to_action=RocqTacticAction,
        ...     to_action_with_retry=lambda t, r, n: RocqRetryAction(t, r, n),
        ...     rectifier=my_llm_rectifier,
        ...     max_retries=3,
        ... )
    """

    def __init__(
        self,
        generator: CandidateGenerator,
        get_state_desc: Callable[[StateT], str | None],
        to_action: Callable[[str], Action[StateT]],
        to_action_with_retry: Callable[
            [str, CandidateRectifier | None, int], Action[StateT]
        ]
        | None = None,
        rectifier: CandidateRectifier | None = None,
        max_retries: int = 0,
    ) -> None:
        """
        Initialize a generator-based strategy.

        Args:
            generator: Produces candidates from state description
            get_state_desc: Extracts string description from state (e.g., goal)
                           Returns None if state is not applicable
            to_action: Converts candidate text to executable Action (simple)
            to_action_with_retry: Converts candidate to retry-capable Action
                                 Signature: (text, rectifier, max_retries) -> Action
                                 If None, rectification is disabled
            rectifier: Optional rectifier for failed candidates
            max_retries: Number of rectification attempts (0 = disabled)
        """
        self._generator = generator
        self._get_state_desc = get_state_desc
        self._to_action = to_action
        self._to_action_with_retry = to_action_with_retry
        self._rectifier = rectifier
        self._max_retries = max_retries

    def rollout(
        self,
        state: StateT,
        max_rollout: int | None = None,
        context: Strategy.Context | None = None,
    ) -> Strategy.Rollout[StateT]:
        """
        Generate actions by converting candidates to domain-specific Actions.

        Args:
            state: Current domain state
            max_rollout: Maximum number of actions to generate
            context: Optional context (passed through, not used)

        Yields:
            (logprob, Action) pairs in descending probability order
        """
        state_desc = self._get_state_desc(state)
        if state_desc is None:
            return  # No description = no candidates

        for candidate in self._generator.generate(state_desc, limit=max_rollout):
            # Use retry-capable action if rectifier is enabled and available
            if (
                self._max_retries > 0
                and self._rectifier is not None
                and self._to_action_with_retry is not None
            ):
                action = self._to_action_with_retry(
                    candidate.text,
                    self._rectifier,
                    self._max_retries,
                )
            else:
                action = self._to_action(candidate.text)

            yield (candidate.logprob, action)

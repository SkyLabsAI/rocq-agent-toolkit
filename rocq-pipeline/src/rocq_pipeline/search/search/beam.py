from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from observability import trace_context
else:
    try:
        from observability import trace_context
    except ImportError:
        from contextlib import contextmanager

        @contextmanager
        def trace_context(_name: str):  # type: ignore[no-redef]
            class DummySpan:
                def set_attribute(self, _key: str, _value: Any) -> None:
                    pass

            yield DummySpan()


from rocq_pipeline.search.strategy import Strategy

from .frontier import PQueue, SavingSolutions, SingleDepth
from .guidance import Guidance, UniformGuidance
from .search import Node, search


class StateManip[T]:
    """Helper for managing imperative state (e.g., RocqCursor)."""

    def freshen(self, state: T) -> T:
        """Create a fresh copy of the state for exploration."""
        return state

    def dispose(self, _state: T) -> None:
        """Clean up a state that's no longer needed."""
        return None


class BeamSearch[T]:
    """
    Beam search implementation using the frontier/search infrastructure.

    This implementation uses:
    - PQueue for priority-based ordering with guidance scores
    - SingleDepth for beam-like behavior (only expand one depth level at a time)
    - SavingSolutions to track solutions
    """

    def __init__(
        self,
        strategy: Strategy[T],
        guidance: Guidance[T] | None = None,
        is_solved: Callable[[T], bool] | None = None,
        beam_width: int = 5,
        explore_width: int = 10,
        max_depth: int = 10,
        stop_on_first_solution: bool = False,
        freshen: StateManip[T] | None = None,
        state_key: Callable[[T], Any] | None = None,
    ) -> None:
        """
        Initialize beam search.

        Args:
            strategy: Strategy for generating actions
            guidance: Guidance function for scoring states (lower is better)
            is_solved: Function to check if a state is a solution
            beam_width: Number of nodes to expand per depth level
            explore_width: Number of actions to try per node
            max_depth: Maximum search depth
            stop_on_first_solution: Whether to stop after finding first solution
            freshen: StateManip for cloning/disposing imperative states
            state_key: Optional function to generate keys for state deduplication
        """
        self._strategy = strategy
        self._guidance = guidance or UniformGuidance()
        self._is_solved = is_solved or (lambda _: False)
        self._beam_width = beam_width
        self._explore_width = explore_width
        self._max_depth = max_depth
        self._stop_on_first = stop_on_first_solution
        self._freshen = freshen or StateManip()
        self._state_key = state_key

    def search(self, start_state: T) -> list[T]:
        """
        Run beam search from the start state.

        Returns:
            List of solution states found
        """
        with trace_context("beam_search") as span:
            span.set_attribute("beam_width", self._beam_width)
            span.set_attribute("explore_width", self._explore_width)
            span.set_attribute("max_depth", self._max_depth)

            # Create the solutions frontier that we'll retrieve results from
            solutions_frontier: SavingSolutions[Node[T], Any] | None = None

            def make_frontier() -> SavingSolutions[Any, Any]:
                nonlocal solutions_frontier

                def scorer(node_with_depth: tuple[Node[T], int]) -> float:
                    # SingleDepth wraps nodes as (node, depth) tuples for its base frontier
                    node, depth = node_with_depth
                    # Combine guidance score with depth for tie-breaking
                    guidance_score = self._guidance.score(node.state, logprob=None)
                    # Add small depth penalty to prefer shorter paths
                    return guidance_score + depth * 0.001

                def is_solution_node(node: Node[T]) -> bool:
                    return self._is_solved(node.state)

                # Create frontier composition
                # PQueue works on (Node[T], int) tuples because SingleDepth wraps them
                base = PQueue(scorer, lambda a, b: (a > b) - (a < b))
                beam = SingleDepth(base)
                solutions_frontier = SavingSolutions(
                    beam, is_solution_node, self._stop_on_first
                )
                return solutions_frontier

            # State management functions for search
            def clone_state(state: T) -> T:
                return self._freshen.freshen(state)

            def dispose_state(state: T) -> None:
                self._freshen.dispose(state)

            # Run search - it will loop internally until frontier is empty or solutions found
            search(
                strategy=self._strategy,
                start=start_state,
                frontier=make_frontier,
                beam_width=self._beam_width,
                explore_width=self._explore_width,
                clone_state=clone_state,
                dispose_state=dispose_state,
                max_depth=self._max_depth,
                state_key=self._state_key,
            )

            # Extract solution states from the frontier
            if solutions_frontier is not None:
                return [node.state for node in solutions_frontier.solutions()]
            return []

import itertools
import uuid
from dataclasses import dataclass
from typing import Any, List, Optional, Tuple, override

from core.config import SearchConfig
from core.types import SearchResult

# Protocols/Interfaces
from domains.base import Domain
from domains.base_goal_tracker import GoalTracker
from rocq_doc_manager.rocq_cursor import RocqCursor
from rocq_pipeline.agent.proof.strategy import Strategy


class BeamNode[T]:
    """Node in the heuristic beam search tree.

    Similar to Beam but with additional fields for heuristic search.
    """

    id: str
    parent_id: Optional[str]
    depth: int
    tactic_history: list[ActionStep]  # this should be extractable from the cursor
    cursor: T
    # active_goals: List[str]
    cost_score: float = float("inf")  # alpha * logProb_of_node + costing
    created_ts: float = field(default_factory=time.time)
    # state: Optional[Any] = None  # Domain-specific state (LeanState, RocqCursor, etc.)
    cumulative_log_prob: float = 0.0  # Cumulative sum of per-tactic average log probs (each tactic's log prob is avg of its tokens)

    def spawn(self, step: ActionStep, state: Optional[Any] = None) -> "BeamNode":
        """Create a child node from this node."""
        # Each tactic_log_prob is already the average of token log probs for that tactic
        # Add current tactic's average to parent's cumulative sum of tactic averages
        new_cumulative_log_prob = self.cumulative_log_prob
        if step.tactic_log_prob is not None:
            new_cumulative_log_prob += step.tactic_log_prob

        return BeamNode(
            id=str(uuid.uuid4()),
            parent_id=self.id,
            depth=self.depth + 1,
            tactic_history=self.tactic_history + [step],
            active_goals=list(step.goal_states),
            state=state,
            cumulative_log_prob=new_cumulative_log_prob,
        )

    def as_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for logging."""
        return {
            "id": self.id,
            "parent": self.parent_id,
            "depth": self.depth,
            "cost_score": self.cost_score,
            "cumulative_log_prob": self.cumulative_log_prob,
            "active_goals": self.active_goals,
            "steps": [dataclasses.asdict(s) for s in self.tactic_history],
        }


class ActionBeamSearch[T]:
    """
    Stub illustrating the internal logic of Action-level Beam Search.

    The search maintains a 'frontier' of proof states and iteratively
    expands them by asking an LLM for tactics and verifying them in Rocq.
    """

    def __init__(
        self,
        interface: Domain,
        config: SearchConfig,
        goal_tracker: GoalTracker,
        strategy: Strategy[T],
        **kwargs,
    ):
        self.interface = interface
        self.config = config
        self.goal_tracker = goal_tracker
        self.heuristic: Guidance[T] | None = kwargs.get("heuristic")
        self.session = kwargs.get("session")
        self._strategy = strategy

    def search(self, problem: str, initial_goals: List[str]) -> SearchResult:
        """
        Main search loop: Depth-first expansion up to max_depth.
        """
        # 1. Initialize root node from session.initial_state
        root = BeamNode(
            id=str(uuid.uuid4()),
            active_goals=initial_goals,
            state=self.session.initial_state,  # The starting RocqCursor
            cost_score=0.0,
        )

        frontier = [root]
        solutions = []

        for depth in range(self.config.max_depth):
            if not frontier or self._is_budget_depleted():
                break

            # 2. Select top 'beam_size' nodes to expand
            nodes_to_expand = frontier[: self.config.beam_size]
            next_frontier = []

            for node in nodes_to_expand:
                # 3. Expansion Step
                children = self._expand_node(node, problem)

                for child in children:
                    if child.is_solved():
                        solutions.append(child)
                    else:
                        next_frontier.append(child)

            # 4. Sort next frontier by cost (Heuristic score + Tactic LogProbs)
            next_frontier.sort(key=lambda n: n.cost_score)
            frontier = next_frontier

        return SearchResult(
            success=len(solutions) > 0, best_beam=solutions[0] if solutions else None
        )

    def _expand_node(self, node: BeamNode, root_problem: str) -> list[BeamNode]:
        """
        Internal loop: Generate -> Verify (with Retries) -> Score
        """
        children: list[BeamNode] = []

        # A. LLM INVOCATION: Generate N candidate tactics (branch_factor)
        # Uses interface.format_action_prompt() to build context
        candidates = self._strategy.rollout(
            node.cursor, max_rollout=self.config.branch_factor
        )

        for action_logprob, action in itertools.islice(
            candidates, self.config.branch_factor
        ):
            # TODO: Wrap this block in an OpenTelemetry span that contains the information
            # about the node in the search. This way we can localize the actions taken during
            # interaction
            action_cursor = node.cursor.clone()
            if not action.interact(action_cursor):
                continue

            cumulative_log_prob = node.cumulative_log_prob + action_logprob

            h_score = self.heuristic.score(action_cursor) if self.heuristic else 0.0
            # TODO: Fix this computation
            total_cost = cumulative_log_prob + h_score

            child_node = BeamNode(
                str(uuid.uuid4()),
                node.id,
                node.depth + 1,
                [],
                action_cursor,
                total_cost,
                time.time(),
            )
            children.append(child_node)

        return children

    def _is_invalid(self, tactic: str, history: list[str]) -> bool:
        """
        Pruning Logic:
        - Returns True if tactic contains 'sorry' or 'admit'.
        - Returns True if tactic repeats a failed or recent pattern too many times.
        """
        if any(bad in tactic for bad in ["sorry", "admit", "Give Up"]):
            return True
        if self._check_repetition(tactic, history):
            return True
        return False

    def _check_repetition(self, tactic: str, history: list[str]) -> bool:
        return False

    def _is_budget_depleted(self) -> bool:
        # Check time, max_expansions, or token usage
        return False

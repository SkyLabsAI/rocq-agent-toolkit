from dataclasses import dataclass, field
from typing import Any, List, Optional, Dict
import time

@dataclass
class SearchConfig:
    beam_size: int = 5
    max_depth: int = 32
    max_expansions: int = 1000
    token_budget: Optional[int] = None
    parallel_beams: int = 1
    stop_when_first_finishes: bool = True
    # Heuristic
    scoring_mode: str = "heuristic_only"
    alpha_distance_weight: float = 0.5
    n_max_distance: float = 10.0

@dataclass
class ActionStep:
    index: int
    tactic: str
    goal_states: List[str]
    tactic_log_prob: Optional[float] = None
    cost_score: float = 0.0
    raw_model_output: str = ""

@dataclass
class BeamNode:
    id: str
    parent_id: Optional[str]
    depth: int
    tactic_history: List[ActionStep]
    active_goals: List[str]
    state: Any  # Generic State T
    cost_score: float = float("inf")
    cumulative_log_prob: float = 0.0
    created_ts: float = field(default_factory=time.time)

    def spawn(self, step: ActionStep, state: Any, new_cost: float, new_log_prob: float) -> "BeamNode":
        import uuid
        return BeamNode(
            id=str(uuid.uuid4()),
            parent_id=self.id,
            depth=self.depth + 1,
            tactic_history=self.tactic_history + [step],
            active_goals=list(step.goal_states),
            state=state,
            cost_score=new_cost,
            cumulative_log_prob=new_log_prob
        )

@dataclass
class SearchResult:
    success: bool
    best_beam: Optional[BeamNode]
    all_solutions: List[BeamNode]
    total_expansions: int
    stop_reason: str
    elapsed_seconds: float
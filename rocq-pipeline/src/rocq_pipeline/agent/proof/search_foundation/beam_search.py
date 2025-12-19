import time
import uuid
from typing import List, Optional, TypeVar, Generic
from concurrent.futures import ThreadPoolExecutor, as_completed

from .types import BeamNode, SearchResult, SearchConfig, ActionStep
from .protocols import Strategy, Guidance, Logger, StateT

T = TypeVar("T", bound=StateT)

class ActionBeamSearch(Generic[T]):
    def __init__(
        self,
        config: SearchConfig,
        strategy: Strategy[T],
        logger: Logger,
        initial_state: T,
        guidance: Optional[Guidance[T]] = None,
    ):
        self.config = config
        self.strategy = strategy
        self.logger = logger
        self.initial_state = initial_state
        self.guidance = guidance
        self.expansions = 0

    def search(self, problem_statement: str) -> SearchResult:
        start_time = time.time()
        root = BeamNode(
            id=str(uuid.uuid4()), parent_id=None, depth=0,
            tactic_history=[], active_goals=self.initial_state.get_goals(),
            state=self.initial_state, cost_score=0.0
        )
        
        frontier: List[BeamNode] = [root]
        solutions: List[BeamNode] = []
        stop_reason = ""

        with ThreadPoolExecutor(max_workers=max(1, self.config.parallel_beams)) as executor:
            for depth in range(self.config.max_depth):
                if not frontier:
                    stop_reason = "exhausted"
                    break

                frontier.sort(key=lambda n: n.cost_score)
                nodes_to_expand = frontier[:self.config.beam_size]
                next_frontier: List[BeamNode] = []
                
                futures = [executor.submit(self._expand_node, node) for node in nodes_to_expand]

                for future in as_completed(futures):
                    children = future.result()
                    for child in children:
                        if not child.active_goals:
                            solutions.append(child)
                        else:
                            next_frontier.append(child)
                frontier = next_frontier
                
                if solutions and self.config.stop_when_first_finishes:
                    stop_reason = "solved"
                    break
        
        elapsed = time.time() - start_time
        return SearchResult(
            success=len(solutions) > 0,
            best_beam=solutions[0] if solutions else (frontier[0] if frontier else None),
            all_solutions=solutions,
            total_expansions=self.expansions,
            stop_reason=stop_reason,
            elapsed_seconds=elapsed
        )

    def _expand_node(self, node: BeamNode) -> List[BeamNode]:
        if node.depth >= self.config.max_depth: return []
        
        candidates = list(self.strategy.rollout(node, node.state, self.config.token_budget))
        children = []

        for logprob, action in candidates:
            success, new_goals, next_state, cost_penalty = action.interact(node.state)
            
            if success:
                h_score = 0.0
                if self.guidance and next_state:
                    h_score, _ = self.guidance.score(next_state, node)

                # TODO: NEEDS CORRECTION
                total_cost = node.cumulative_log_prob + (-logprob) + h_score + cost_penalty
                
                step = ActionStep(
                    index=len(node.tactic_history), tactic=action.to_text(),
                    goal_states=new_goals, tactic_log_prob=logprob,
                    raw_model_output=str(action.get_metadata())
                )
                
                child = node.spawn(step, next_state, total_cost, node.cumulative_log_prob + (-logprob))
                children.append(child)
        
        self.expansions += 1
        return children
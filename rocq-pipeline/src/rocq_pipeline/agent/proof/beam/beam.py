"""
Rocq-Specific Beam Search Implementation.
Adapts the Generic Search Foundation to the Rocq Environment.
"""
from typing import List, Optional, Tuple
from rocq_doc_manager import RocqCursor

# Import the Generic Foundation
from ...search_foundation.beam_search import ActionBeamSearch as GenericActionBeamSearch
from ...search_foundation.types import SearchConfig, SearchResult
from ...search_foundation.protocols import Strategy, Guidance, Logger, StateT
from ...proof_state import ProofState

# 1. The Adapter (Makes RocqCursor look like StateT)
class RocqStateAdapter(StateT):
    def __init__(self, cursor: RocqCursor):
        self.cursor = cursor

    def get_goals(self) -> List[str]:
        return self.get_goals_from_cursor(self.cursor)

    def apply_tactic(self, tactic: str) -> Tuple[bool, List[str], Optional["RocqStateAdapter"], Optional[str]]:
        # Clone cursor first so we don't mutate the parent state on failure.
        next_cursor = self.cursor.clone()
        res = next_cursor.run_command(tactic)

        if isinstance(res, RocqCursor.Err):
            next_cursor.dispose()
            return False, [], None, res.message

        # Success - get new goals
        new_goals = self.get_goals_from_cursor(next_cursor)
        return True, new_goals, RocqStateAdapter(next_cursor), None

    def format_prompt_context(self) -> dict:
        return {
            "goals": self.get_goals(),
            "history": "..." # logic to get history if we decide to use it
        }

    # Helper
    def get_goals_from_cursor(self, c):
        goal_reply = c.current_goal()
        if isinstance(goal_reply, RocqCursor.Err):
            return []
        proof_state = ProofState(goal_reply)
        return [f"{g}\n{g.parts.rocq_concl}" for g in proof_state.goals.values()]

# 2. The Specific Search Class (Optional Wrapper)
class RocqActionBeamSearch(GenericActionBeamSearch[RocqStateAdapter]):
    """
    Rocq-Specific instantiation of the Generic Search.
    Ensures that we strictly use RocqStateAdapter.
    """
    def __init__(
        self,
        config: SearchConfig,
        strategy: Strategy[RocqStateAdapter], # Enforce specific type
        logger: Logger,
        initial_cursor: RocqCursor,
        guidance: Optional[Guidance[RocqStateAdapter]] = None,
    ):
        # Wrap the raw cursor in the adapter before passing to generic engine
        adapter = RocqStateAdapter(initial_cursor)
        super().__init__(config, strategy, logger, adapter, guidance)

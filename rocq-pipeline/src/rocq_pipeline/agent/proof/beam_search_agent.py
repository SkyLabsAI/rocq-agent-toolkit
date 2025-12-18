from typing import override
# from pathlib import Path
from rocq_doc_manager import RocqCursor

from rocq_pipeline.agent.base import ProofAgent, TaskResult, TacticApplication
from rocq_pipeline.proof_state import ProofState, RocqGoal

# Imports from beam search framework
from core.config import SearchConfig
from core.logger import NDJSONLogger
from search.action_search import ActionBeamSearch
from domains.rocq import RocqInterface
from domains.rocq_goal_tracker import RocqGoalTracker


# This is a wrapper class that aligns with our Lean Implementation
# It will exist in the Beam Search Code
# We will not ever "close" an rdm session when integrating with RAT 
class RocqSession:
    """Session wrapper to align Rocq with the Beam Search protocol."""
    def __init__(self, rdm: RocqCursor):
        self._rdm = rdm

    @property
    def initial_state(self) -> RocqCursor:
        """Returns the starting cursor for the search root node."""
        return self._rdm

    def close(self):
        """Disposes the underlying cursor."""
        self._rdm.dispose()


class BeamSearchAgent(ProofAgent):
    """
    A proof agent that uses beam search to find proofs."""
    
    def __init__(
        self,
        generator_url: str,
        generator_model: str,
        workspace: str, # this is a lean specific
        rocq_file: str,
        beam_size: int = 5,
        max_depth: int = 32,
        branch_factor: int = 4,
        max_seconds: float | None = None,
        max_retries: int = 0,
        log_dir: str = "runs",
        run_name: str = "beam_search_agent",
    ) -> None:
        super().__init__(goal_ty_upperbound=RocqGoal)
        self.generator_url = generator_url
        self.generator_model = generator_model
        self.workspace = workspace
        self.rocq_file = rocq_file
        self.beam_size = beam_size
        self.max_depth = max_depth
        self.branch_factor = branch_factor
        self.max_seconds = max_seconds
        self.max_retries = max_retries
        self.log_dir = log_dir
        self.run_name = run_name
        self._history: list[TacticApplication] = []
    
    @override
    def prove(self, rdm: RocqCursor) -> TaskResult:

        # ------------- PASS RDM TO BEAM SEARCH AND COMPLETE THE SEARCH -------------
        
        
        # 1. Create beam search components
        # RocqSession wrapper to provide session.initial_state for ActionBeamSearch
        session = RocqSession(rdm)

        # RocqInterface for prompt formatting (takes workspace, not session)
        interface = RocqInterface(
            workspace=self.workspace,
            mode="cursor",
            rocq_file=self.rocq_file,
        )
        
        # Action Beam Search Specific Params
        config = SearchConfig(
            mode="action",
            domain="rocq",
            beam_size=self.beam_size,
            max_depth=self.max_depth,
            branch_factor=self.branch_factor,
            max_seconds=self.max_seconds,
            max_retries=self.max_retries,
            generator_url=self.generator_url,
            generator_model=self.generator_model,
            prover_workspace=self.workspace, # Corrected field name
            rocq_file=self.rocq_file,
        )
        
        logger = NDJSONLogger(log_dir=self.log_dir, run_name=self.run_name)
        
        # RocqGoalTracker now takes the session wrapper
        goal_tracker = RocqGoalTracker(cfg=config, session=session)
        
        # ActionBeamSearch with goal_tracker and session wrapper
        search = ActionBeamSearch(
            interface=interface,
            config=config,
            logger=logger,
            goal_tracker=goal_tracker,
            heuristic=None,  # Optional
            session=session,  # Uses RocqSession for initial_state protocol
        )
        
        # Extract initial goals
        initial_goals = self._extract_initial_goals(rdm)
        problem = self._get_theorem_statement(rdm)
        
        result = search.search(problem=problem, initial_goals=initial_goals)
        
        if not result.success:
            return self.give_up(rdm, message=f"No proof found: {result.stop_reason}")
        
        # -------------- REPLAY PROOF ON ORIGINAL CURSOR --------------
        
        
        # 2. Replay proof on original cursor
        self._history = []
        for tactic in result.best_beam.actions:
            if not tactic.endswith('.'):
                tactic += '.'
            tac_app = self.run_tactic(rdm, tactic)
            self._history.append(tac_app)
            # This branch should never be reached if the search is successful
            if tac_app.err:
                return self.give_up(rdm, reason=tac_app.err)
        
        return self.finished(rdm, side_effects={"proof": result.best_beam.actions})
    
    # Private Helper Methods 
    def _extract_initial_goals(self, rdm: RocqCursor) -> list[str]:
        """Extract initial goals from cursor."""
        goal_reply = rdm.current_goal()
        if isinstance(goal_reply, RocqCursor.Err):
            return []
        
        proof_state = ProofState(goal_reply)
        # Formatted with conclusion for better LLM context, matching framework standards
        return [f"{g}\n{g.parts.rocq_concl}" for g in proof_state.goals.values()]
    
    def _get_theorem_statement(self, rdm: RocqCursor) -> str:
        """Get theorem statement being proven.
        
        This attempts to find the last relevant command in the document prefix.
        """
        prefix = rdm.doc_prefix()
        if not prefix:
            return ""
        
        # Look backwards for something that looks like a theorem
        # This is a heuristic and might need improvement
        keywords = ["Theorem", "Lemma", "Goal", "Instance", "Fact", "Remark", "Corollary", "Property", "Proposition"]
        for item in reversed(prefix):
           if any(k in item.text for k in keywords):
               return item.text
               
        return ""
    
    # is this function needed somewhere in RAT? 
    #only kept in since it is in TraceAgent
    def history(self) -> list[TacticApplication]:
        return self._history[:]
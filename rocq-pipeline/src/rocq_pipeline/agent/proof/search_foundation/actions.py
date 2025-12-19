from typing import Optional, List, Any, Tuple
from .protocols import Action, StateT, LLMClient

class SelfCorrectingAction(Action[StateT]):
    """
    An action that attempts a tactic, and if it fails, asks an LLM to fix it 
    based on the error message, up to `max_retries` times.
    """
    def __init__(
        self, 
        initial_tactic: str, 
        llm: LLMClient,
        context_prompt: str,
        max_retries: int = 2
    ):
        self.tactic = initial_tactic
        self.llm = llm
        self.context = context_prompt
        self.max_retries = max_retries
        
        # Telemetry
        self.attempts = 0
        self.final_tactic = initial_tactic
        self.trace = []

    def interact(self, state: StateT) -> Tuple[bool, List[str], Optional[StateT], float]:
        current_tactic = self.tactic
        
        for attempt in range(self.max_retries + 1):
            self.attempts += 1
            
            # 1. Apply (Abstracted via State Protocol)
            # Note: We must clone the state or rely on the domain to return a new state
            # so we don't corrupt the parent node if we fail.
            success, new_goals, next_state, error_msg = state.apply_tactic(current_tactic)
            
            self.trace.append({
                "attempt": attempt,
                "tactic": current_tactic,
                "success": success,
                "error": error_msg
            })
            
            # Success path
            if success:
                self.final_tactic = current_tactic
                return True, new_goals, next_state, 0.0

            # Failure path - Generate Correction
            if attempt < self.max_retries and error_msg:
                try:
                    fix_prompt = self._build_fix_prompt(current_tactic, error_msg)
                    # Helper call to LLM (n=1)
                    corrections = self.llm.generate(fix_prompt, n=1)
                    if corrections:
                        current_tactic = corrections[0][0].strip() # Update for next loop
                    else:
                        break # LLM failed to answer
                except Exception:
                    break # Transport error

        return False, [], None, 0.0

    def _build_fix_prompt(self, failed_tactic: str, error: str) -> str:
        # Generic prompt engineering
        return (
            f"{self.context}\n\n"
            f"The tactic `{failed_tactic}` failed with error:\n{error}\n\n"
            "Please provide a corrected tactic. Output only the tactic code."
        )

    def to_text(self) -> str:
        return self.final_tactic

    def get_metadata(self) -> dict:
        return {"retries": self.attempts - 1, "trace": self.trace}
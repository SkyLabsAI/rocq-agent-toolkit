from rocq_doc_manager import RocqCursor

from ..proof_state import ProofState
from .extractor import DefaultDocumentWatcher, StateExtractor, TrivialBracketedExtractor


class ExtractGoalAsString(StateExtractor[str]):
    """A simple extractor that just gets the current goal the way it is printed in Rocq."""

    def extract(self, rdm: RocqCursor) -> str:
        result = rdm.current_goal()
        if isinstance(result, rdm.Err):
            raise RuntimeError("Failed to parse goal: {result}")
        return str(ProofState(result))


class GoalAsString(
    DefaultDocumentWatcher, TrivialBracketedExtractor[str], ExtractGoalAsString
):
    pass

def build() -> GoalAsString:
    return GoalAsString()
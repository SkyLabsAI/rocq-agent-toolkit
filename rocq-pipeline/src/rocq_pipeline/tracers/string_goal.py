from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_pipeline.proof_state import ProofState

from .extractor import DefaultDocumentWatcher, StateExtractor, TrivialBracketedExtractor


class ExtractGoalAsString(StateExtractor[str]):
    """A simple extractor that just gets the current goal the way it is printed in Rocq."""

    async def extract(self, rdm: RocqCursor) -> str:
        result = await rdm.current_goal()
        if isinstance(result, rdm_api.Err):
            raise RuntimeError("Failed to parse goal: {result}")
        return str(ProofState(result))


class GoalAsString(
    DefaultDocumentWatcher, TrivialBracketedExtractor[str], ExtractGoalAsString
):
    pass


def build() -> GoalAsString:
    return GoalAsString()

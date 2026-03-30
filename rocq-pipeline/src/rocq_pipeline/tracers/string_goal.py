from rocq_doc_manager import RocqCursor

from .extractor import DefaultDocumentWatcher, StateExtractor, TrivialBracketedExtractor


class ExtractGoalAsString(StateExtractor[list[str]]):
    """A simple extractor that just gets the current goal the way it is printed in Rocq."""

    async def extract(self, rc: RocqCursor) -> list[str]:
        result = await rc.current_goal()
        if result is None:
            return []
        return result.focused_goals


class GoalAsString(
    DefaultDocumentWatcher, TrivialBracketedExtractor[list[str]], ExtractGoalAsString
):
    pass


def build() -> GoalAsString:
    return GoalAsString()

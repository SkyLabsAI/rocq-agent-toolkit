from typing import override

from rocq_doc_manager import RocqCursor

from ..action import Action


class TacticAction(Action[RocqCursor]):
    def __init__(self, tactic: str) -> None:
        self._tactic = tactic

    @override
    def interact(self, rc: RocqCursor) -> bool:
        response = self.run_tactic(rc, self._tactic)
        return not issubclass(type(response), RocqCursor.Err)

    def run_tactic(
        self, rc: RocqCursor, tactic: str
    ) -> RocqCursor.CommandData | RocqCursor.Err[RocqCursor.CommandError]:
        return rc.insert_command(tactic)

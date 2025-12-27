from typing import override

from rocq_doc_manager import RocqCursor

from ..action import Action


class RocqTacticAction(Action[RocqCursor]):
    def __init__(self, tactic: str) -> None:
        self._tactic = tactic

    @override
    def interact(self, state: RocqCursor) -> RocqCursor:
        # TODO: the fact that cursors are not functional is quite annoying here.
        # It should be the caller that creates a new cursor, but in this case
        # we will basically always be returning our own cursor.
        # If cursors were functional, we would just be returning the latest
        # cursor here.
        response = self.run_tactic(state, self._tactic)
        if issubclass(type(response), RocqCursor.Err):
            raise Action.Failed()
        return state

    def run_tactic(
        self, rc: RocqCursor, tactic: str
    ) -> RocqCursor.CommandData | RocqCursor.Err[RocqCursor.CommandError]:
        return rc.insert_command(tactic)

    @override
    def key(self) -> str:
        return self._tactic.strip()

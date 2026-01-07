from typing import Annotated, override

from provenance_toolkit import Provenance
from rocq_doc_manager import RocqCursor

from rocq_pipeline.agent.base import TaskResult

from .markov import MarkovAgent


class ChoiceAgent(MarkovAgent):
    _all_choices: Annotated[list[str], Provenance.Reflect.Field]

    def __init__(self, choices: list[str]):
        super().__init__()
        self._all_choices = choices
        self._check_index: int = 0

    @override
    def next_tac(self, rdm: RocqCursor) -> str | TaskResult:
        if self.last_failed():
            self._check_index += 1
        else:
            self._check_index = 0

        if self._check_index >= len(self._all_choices):
            return self.give_up(
                rdm,
                message="No more tactics to choose from.",
            )

        return f"{self._all_choices[self._check_index]}."

import logging
import re
from typing import override

from rocq_doc_manager import RocqCursor

from rocq_pipeline.schema import task_output

logger = logging.getLogger(__name__)


# The interface
class NotFound(Exception):
    pass


class Locator:
    def __call__(self, rdm: RocqCursor) -> bool:
        return False

    def task_kind(self) -> task_output.TaskKind:
        return task_output.TaskKind(task_output.OtherTask("unknown"))


class FirstAdmit(Locator):
    def __str__(self) -> str:
        return "admit"

    @override
    def __call__(self, rdm: RocqCursor) -> bool:
        def is_admit(
            text: str,
            kind: str,
        ) -> bool:
            return kind == "command" and text.startswith("admit")

        return rdm.advance_to_first_match(is_admit)

    def task_kind(self) -> task_output.TaskKind:
        return task_output.TaskKind(task_output.OtherTask("admit"))


class FirstLemma(Locator):
    def __str__(self) -> str:
        which = f"({self._index})" if self._index != 0 else ""
        if self._style is None:
            return f"lemma:{self._name}{which}"
        else:
            return f"{self._style}:{self._name}{which}"

    def __init__(self, lemma_name: str, style: str | None = None, index: int = 0):
        self._name = lemma_name
        self._style = style
        self._index = index

    @override
    def __call__(self, rdm: RocqCursor) -> bool:
        if self._style is None:
            prefix = "Lemma|Theorem"
        else:
            prefix = self._style

        mtch = re.compile(f"({prefix})\\s+{self._name}[^0-9a-zA-Z_']")

        def is_lemma(
            text: str,
            kind: str,
        ) -> bool:
            return kind == "command" and mtch.match(text) is not None

        if rdm.advance_to_first_match(is_lemma, step_over_match=True):
            for cmd in rdm.doc_suffix():
                if cmd.kind == "blank" or (
                    cmd.kind == "command" and cmd.text.startswith("Proof")
                ):
                    run_step_reply = rdm.run_step()
                    if isinstance(run_step_reply, RocqCursor.Err):
                        logger.warning(f"RocqCursor.run_step failed: {run_step_reply}")
                        return False
                else:
                    return True

        return False

    def task_kind(self) -> task_output.TaskKind:
        return task_output.TaskKind(task_output.FullProofTask())


def parse_locator(s: str) -> Locator:
    def get_index(s: str) -> tuple[str, int]:
        ptrn: re.Pattern = re.compile(r"(.+)\(([0-9]+)\)")
        mtch = ptrn.match(s)
        if mtch is None:
            return (s, 0)
        else:
            return mtch.group(1), int(mtch.group(2))

    if s.startswith("lemma:"):  # Backwards compatibility
        logger.warning(
            " ".join(
                [
                    '"lemma:" locator is deprecated,',
                    'use "Theorem:" or "Lemma:":',
                    s,
                ]
            )
        )
        return FirstLemma(s[len("lemma:") :])
    elif s.startswith("Theorem:"):
        nm, index = get_index(s[len("Theorem:") :])
        return FirstLemma(nm, "Theorem", index=index)
    elif s.startswith("Lemma:"):
        nm, index = get_index(s[len("Lemma:") :])
        return FirstLemma(nm, "Lemma", index=index)
    if s == "admit":
        return FirstAdmit()
    return Locator()

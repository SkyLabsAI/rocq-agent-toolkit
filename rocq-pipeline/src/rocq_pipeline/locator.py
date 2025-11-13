import re
from collections.abc import Callable
from typing import override

from rocq_doc_manager import RocqDocManager

from rocq_pipeline.schema import task_output


def scan_to(rdm: RocqDocManager, fn: Callable[[str], bool]) -> bool:
    suffix = rdm.doc_suffix()
    for cmd in suffix:
        if cmd.kind == "command" and fn(cmd.text):
            return True
        rdm.run_step()
    return False


# The interface
class NotFound(Exception):
    pass


class Locator:
    def __call__(self, rdm: RocqDocManager) -> bool:
        return False

    def task_kind(self) -> task_output.TaskKind:
        return task_output.TaskKind(
            task_output.OtherTask("unknown")
        )


class FirstAdmit(Locator):
    def __str__(self) -> str:
        return 'admit'

    @override
    def __call__(self, rdm: RocqDocManager) -> bool:
        def is_admit(tac: str) -> bool:
            return tac.startswith("admit")

        return scan_to(rdm, is_admit)

    def task_kind(self) -> task_output.TaskKind:
        return task_output.TaskKind(
            task_output.OtherTask("admit")
        )


class FirstLemma(Locator):
    def __str__(self) -> str:
        if self._style is None:
            return f"lemma:{self._name}"
        else:
            return f"{self._style.lower()}:{self._name}"

    def __init__(self, lemma_name: str, style: str | None = None):
        self._name = lemma_name
        self._style = style

    @override
    def __call__(self, rdm: RocqDocManager) -> bool:
        if self._style is None:
            prefix = "Lemma|Theorem"
        else:
            prefix = self._style

        mtch = re.compile(f"({prefix})\\s+{self._name}[^0-9a-zA-Z_]")

        def is_lemma(cmd: str) -> bool:
            return mtch.match(cmd) is not None

        if scan_to(rdm, is_lemma):
            rdm.run_step()  # advance past the lemma statement
            for cmd in rdm.doc_suffix():
                if cmd.kind == "blank" or (
                    cmd.kind == "command" and cmd.text.startswith("Proof")
                ):
                    rdm.run_step()
                else:
                    return True

        return False

    def task_kind(self) -> task_output.TaskKind:
        return task_output.TaskKind(
            task_output.FullProofTask()
        )


def parse_locator(s: str) -> Locator:
    if s.startswith("lemma:"):
        return FirstLemma(s[len("lemma:"):],"Lemma")
    if s == "admit":
        return FirstAdmit()
    return Locator()

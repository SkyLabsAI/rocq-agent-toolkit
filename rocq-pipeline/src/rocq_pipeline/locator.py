from __future__ import annotations
import logging
import re
from typing import Callable, override

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


    parsers: list[Callable[[str], Locator | None]] = []
    @staticmethod
    def register_parser(parser: Callable[[str], Locator | None]) -> None:
        Locator.parsers.append(parser)

    # [FirstLemma.parse, FirstAdmit.parse, MarkerCommentLocator.parse]
    @staticmethod
    def parse_locator(s: str) -> Locator:
        for parser in Locator.parsers:
            loc = parser(s)
            if loc is not None:
                return loc
        return Locator()

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

    @staticmethod
    def parse(s: str) -> FirstAdmit | None:
        if s == "admit":
            return FirstAdmit()
        return None

Locator.register_parser(FirstAdmit.parse)

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
                if cmd.kind != "command" or (
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

    @staticmethod
    def parse(s: str) -> FirstLemma | None:
        def get_index(s: str) -> tuple[str, int]:
            ptrn: re.Pattern = re.compile(r"(.+)\(([0-9]+)\)")
            mtch = ptrn.match(s)
            if mtch is None:
                return (s, 0)
            else:
                return mtch.group(1), int(mtch.group(2))

        for kw in ["Lemma", "Theorem"]:
            kw_colon = kw + ":"
            if s.startswith(kw_colon):
                nm, index = get_index(s[len(kw_colon) :])
                return FirstLemma(nm, kw, index=index)

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

        return None

Locator.register_parser(FirstLemma.parse)

# TODO: add unit tests
class MarkerCommentLocator(Locator):
    """Locates a comment that contains the given string."""

    COMMENT_MARKER_PREFIX = "comment_marker:"

    def __init__(self, marker: str):
        self._marker = marker

    def __str__(self) -> str:
        return f"{self.COMMENT_MARKER_PREFIX}{self._marker}"

    @override
    def __call__(self, rdm: RocqCursor) -> bool:
        def is_marker_comment(
            text: str,
            kind: str,
        ) -> bool:
            return kind == "blanks" and self._marker in text

        return rdm.advance_to_first_match(is_marker_comment)

    def task_kind(self) -> task_output.TaskKind:
        return task_output.TaskKind(task_output.OtherTask(self.__str__()))

    @staticmethod
    def parse(s: str) -> MarkerCommentLocator | None:
        if s.startswith(MarkerCommentLocator.COMMENT_MARKER_PREFIX):
            return MarkerCommentLocator(
                s[len(MarkerCommentLocator.COMMENT_MARKER_PREFIX) :]
            )
        return None

Locator.register_parser(MarkerCommentLocator.parse)

def parse_locator(s: str) -> Locator:
    return Locator.parse_locator(s)


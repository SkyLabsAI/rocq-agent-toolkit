from __future__ import annotations

import logging
import re
from collections.abc import Callable
from typing import override

from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api

logger = logging.getLogger(__name__)


class Locator:
    """A Locator refers to search for a line within a Rocq document.

    Beyond __call__, implementers must override '__str__'."""

    def __call__(self, rc: RocqCursor) -> bool:
        """Move the cursor to the line identified by the Locator."""
        return False

    @override
    def __eq__(self, other: object) -> bool:
        if type(other) is type(self):
            return str(self) == str(other)
        return False


class LocatorParser:
    parsers: list[Callable[[str], Locator]] = []

    @staticmethod
    def register_parser(parser: Callable[[str], Locator]) -> None:
        LocatorParser.parsers.append(parser)

    @staticmethod
    def parse(s: str) -> Locator:
        for parser in LocatorParser.parsers:
            try:
                return parser(s)
            except ValueError:
                continue
        raise ValueError(f"Failed to parse locator from `{s}`")


class FirstAdmit(Locator):
    """Find the first (or nth) use of the `admit` tactic."""

    def __init__(self, index: int = 0) -> None:
        self._index = index

    def __str__(self) -> str:
        if self._index == 0:
            return "admit"
        return f"admit({self._index})"

    @override
    def __call__(self, rc: RocqCursor) -> bool:
        def is_admit(
            text: str,
            kind: str,
        ) -> bool:
            return kind == "command" and text.startswith("admit")

        return rc.goto_first_match(is_admit, skip=self._index)

    PTRN_PARSE = re.compile(r"admit(\([0-9]+\))?")

    @staticmethod
    def parse(s: str) -> FirstAdmit:
        if not (mtch := FirstAdmit.PTRN_PARSE.match(s)):
            raise ValueError(f"Failed to parse FirstAdmit from '{s}'")
        if mtch.group(1):
            try:
                index: int = int(mtch.group(1)[1:-1])
            except BaseException as err:
                raise ValueError(
                    f"Failed to parse integer from '{mtch.group(1)}'."
                ) from err
            return FirstAdmit(index)
        return FirstAdmit()


LocatorParser.register_parser(FirstAdmit.parse)


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
    def __call__(self, rc: RocqCursor) -> bool:
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

        if rc.goto_first_match(is_lemma, step_over_match=True, skip=self._index):
            for cmd in rc.doc_suffix():
                if cmd.kind != "command" or (
                    cmd.kind == "command" and cmd.text.startswith("Proof")
                ):
                    run_step_reply = rc.run_step()
                    if isinstance(run_step_reply, rdm_api.Err):
                        logger.warning(f"RocqCursor.run_step failed: {run_step_reply}")
                        return False
                else:
                    return True

        return False

    @staticmethod
    def parse(s: str) -> FirstLemma:
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

        raise ValueError(f"Failed to parse FirstLemma from '{s}'")


LocatorParser.register_parser(FirstLemma.parse)


class CommentMarkerLocator(Locator):
    """Locates a comment that contains the given string."""

    PREFIX = "comment_marker"
    PTRN_PARSE = re.compile(r"comment_marker(\([0-9]+\))?:")

    def __init__(self, marker: str, index: int = 0):
        self._marker = marker
        self._index = index

    def __str__(self) -> str:
        if self._index:
            return f"{CommentMarkerLocator.PREFIX}({self._index}){self._marker}"
        return f"{CommentMarkerLocator.PREFIX}{self._marker}"

    @override
    def __call__(self, rc: RocqCursor) -> bool:
        def is_marker_comment(
            text: str,
            kind: str,
        ) -> bool:
            return kind == "blanks" and self._marker in text

        return rc.goto_first_match(is_marker_comment)

    @staticmethod
    def parse(s: str) -> CommentMarkerLocator:
        if not (mtch := CommentMarkerLocator.PTRN_PARSE.match(s)):
            raise ValueError(f"Failed to parse 'CommentMarkerLocator' from {s}")
        marker = s[len(mtch.group(0)) :]
        if mtch.group(1):
            try:
                return CommentMarkerLocator(marker, int(mtch.group(1)[1:-1]))
            except ValueError as err:
                raise ValueError(
                    f"Failed to parse 'CommentMarkerLocator' from {s}"
                ) from err
        return CommentMarkerLocator(marker, 0)


LocatorParser.register_parser(CommentMarkerLocator.parse)

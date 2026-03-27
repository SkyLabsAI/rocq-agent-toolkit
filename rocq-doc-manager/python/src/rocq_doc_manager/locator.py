from __future__ import annotations

import logging
import re
from collections.abc import Callable
from typing import override
from warnings import deprecated

from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api

logger = logging.getLogger(__name__)


class Locator:
    """A Locator refers to search for a line within a Rocq document.

    Beyond __call__, implementers must override '__str__'."""

    @deprecated("use `go_to`")
    async def __call__(self, rc: RocqCursor, *, next: bool = False) -> bool:
        return await self.go_to(rc, next=next)

    async def go_to(self, rc: RocqCursor, *, next: bool = False) -> bool:
        """Move the cursor to the line identified by the Locator.

        If `next` is True, then the search occurs **forward** from the
        current position of the RocqCursor.
        """
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
    async def go_to(self, rc: RocqCursor, *, next: bool = False) -> bool:
        def is_admit(item: rdm_api.PrefixItem | rdm_api.SuffixItem) -> bool:
            return item.kind == "command" and item.text.startswith("admit")

        return await rc.goto_first_match(
            is_admit, skip=self._index, include_prefix=not next
        )

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
    """Finds the lemma or theorem with the given name.
    The cursor is placed at the **beginning of the proof script for the lemma**.

    The proof starts either:
    - immediately *before* the `Proof (term).` command -- this is very uncommon.
    - immediately after the `Proof` command
    - immediately before the first non-blank interaction.
    """

    _PROOF_TERM = re.compile(r"^Proof\s+(?!\s)(?!\.\s)(.*)\.\s*$", flags=re.DOTALL)

    def __str__(self) -> str:
        which = f"({self._index})" if self._index != 0 else ""
        if self._style is None:
            return f"lemma:{self._name}{which}"
        else:
            return f"{self._style}:{self._name}{which}"

    # _DEFAULT_STYLE = "Theorem|Lemma|Fact|Remark|Property|Proposition|Corollary"
    _DEFAULT_STYLE = "Lemma|Theorem"

    def __init__(self, lemma_name: str, style: str | None = None, index: int = 0):
        self._name = lemma_name
        self._name_re = re.compile(self._name)
        self._style = style
        self._style_re = re.compile(self._DEFAULT_STYLE if style is None else style)
        self._index = index

    @override
    async def go_to(self, rc: RocqCursor, *, next: bool = False) -> bool:
        def is_lemma(item: rdm_api.PrefixItem | rdm_api.SuffixItem) -> bool:
            return (
                item.data is not None
                and item.data.kind == "StartTheoremProof"
                and "Fail" not in item.data.controls
                and "Succeed" not in item.data.controls
                and any(
                    self._name_re.fullmatch(id) is not None
                    for id in item.data.attrs["ids"]
                )
                and self._style_re.fullmatch(item.data.attrs["kind"]) is not None
            )

        if await rc.goto_first_match(
            is_lemma, step_over_match=True, skip=self._index, include_prefix=not next
        ):
            # Scan for the `Proof` command following the description of the class.
            for cmd in await rc.doc_suffix():
                if cmd.kind == "blanks":
                    await rc.run_step()
                    continue

                if cmd.text.startswith("Proof"):
                    # This is a non-closing form of `Proof`, e.g. `Proof with` or `Proof using`.
                    # We step over it.
                    index_before_proof = await rc.cursor_index()
                    run_step_reply = await rc.run_step()
                    if isinstance(run_step_reply, rdm_api.Err):
                        logger.warning(f"RocqCursor.run_step failed: {run_step_reply}")
                        # Even if the step failed, we still found the match.
                    if (await rc.current_goal()) is None:
                        # print("Proof closed goal! Reverting")
                        # If evaluating the `Proof` closed the goal, then we need
                        # to backtrack.
                        await rc.revert_before(erase=False, index=index_before_proof)
                    return True
                else:
                    # This is an interaction that is not a `Proof` command, so we assume that
                    # it is the start of the proof script and we do not step over it.
                    # print("Proof without `Proof` command")
                    return True
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
    async def go_to(self, rc: RocqCursor, *, next: bool = False) -> bool:
        def is_marker_comment(item: rdm_api.PrefixItem | rdm_api.SuffixItem) -> bool:
            return item.kind == "blanks" and self._marker in item.text

        return await rc.goto_first_match(is_marker_comment, include_prefix=not next)

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

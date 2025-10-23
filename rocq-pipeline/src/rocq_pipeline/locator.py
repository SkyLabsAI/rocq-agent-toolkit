"""Locators for finding specific positions in Coq documents.

This module provides various locator implementations that can scan
Coq documents and position the cursor at specific tasks or locations.
"""

import re
from typing import Callable, override

from rocq_doc_manager import RocqDocManager


def scan_to(rdm: RocqDocManager, fn: Callable[[str], bool]) -> bool:
    """Scan a document until reaching a command where the function returns True.

    This function scans through the document suffix, applying the given
    function to each command's text. When the function returns True for
    a command, scanning stops and the command is not evaluated.

    Args:
        rdm: The RocqDocManager instance containing the document.
        fn: A function that takes a command string and returns True if
            the command matches the desired criteria.

    Returns:
        True if a matching command was found, False otherwise.
    """
    suffix = rdm.doc_suffix()
    for cmd in suffix:
        if cmd["kind"] == "command" and fn(cmd["text"]):
            return True
        rdm.run_step()
    return False


# The interface
class NotFound(Exception):
    """Exception raised when a locator fails to find its target."""


class Locator:
    """Base class for document locators.

    A locator is responsible for finding and positioning the cursor
    at a specific location within a Coq document. This base class
    provides the interface that all locators must implement.
    """

    def __call__(self, rdm: RocqDocManager) -> bool:
        """Locate the target position in the document.

        Args:
            rdm: The RocqDocManager instance containing the document.

        Returns:
            True if the target was found and positioned, False otherwise.
        """
        return False


class FirstAdmit(Locator):
    """Locator that finds the first 'admit' command in the file."""

    @override
    def __call__(self, rdm: RocqDocManager) -> bool:
        """Find and position at the first 'admit' command.

        Args:
            rdm: The RocqDocManager instance containing the document.

        Returns:
            True if an 'admit' command was found, False otherwise.
        """

        def is_admit(tac: str) -> bool:
            return tac.startswith("admit")

        return scan_to(rdm, is_admit)


class FirstLemma(Locator):
    """Locator that finds the first lemma with a given name.

    This locator searches for a lemma, theorem, or example with the
    specified name and positions the cursor at the beginning of its proof.
    """

    _name: str
    _style: str | None

    def __init__(self, lemma_name: str, style: str | None = None):
        """Initialize the lemma locator.

        Args:
            lemma_name: The name of the lemma to find.
            style: The type of lemma to search for. If None, searches for
                any definition that opens a proof (Lemma, Theorem, etc.).
                Otherwise, uses the specific type (e.g., 'Lemma', 'Theorem', 'Example').
        """
        self._name = lemma_name
        self._style = style

    @override
    def __call__(self, rdm: RocqDocManager) -> bool:
        """Find and position at the specified lemma.

        Args:
            rdm: The RocqDocManager instance containing the document.

        Returns:
            True if the lemma was found and positioned, False otherwise.
        """
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
                if cmd["kind"] == "blank" or (
                    cmd["kind"] == "command" and cmd["text"].startswith("Proof")
                ):
                    rdm.run_step()
                else:
                    return True

        print("failed to find lemma")
        return False


def parse_locator(s: str) -> Locator:
    """Parse a locator string and return the appropriate locator instance.

    This function creates locator instances based on string descriptions.
    Supported formats:
    - 'lemma:<name>': Creates a FirstLemma locator for the specified lemma name
    - 'admit': Creates a FirstAdmit locator
    - Any other string: Returns a base Locator (which always returns False)

    Args:
        s: The locator string to parse.

    Returns:
        A Locator instance appropriate for the given string.
    """
    if s.startswith("lemma:"):
        return FirstLemma(s[len("lemma:") :])
    if s == "admit":
        return FirstAdmit()
    return Locator()

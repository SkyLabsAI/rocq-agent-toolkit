import os
from collections.abc import Iterator
from contextlib import contextmanager

import pytest
from hypothesis import strategies as st

from rocq_doc_manager import RocqDocManager


class RDM_Tests:
    @staticmethod
    def mk_rdm(
            path: str = "my_fake.v",
            rocq_args: list[str] | None = None
    ) -> RocqDocManager:
        return RocqDocManager(
            [] if rocq_args is None else rocq_args,
            path,
            dune=os.environ.get("RDM_USE_DUNE", "True") == "True",
        )

    @pytest.fixture(scope="class")
    @staticmethod
    def transient_shared_rdm() -> RocqDocManager:
        """A RocqDocManager for a fake file that can't be loaded."""
        return RDM_Tests.mk_rdm()

    @pytest.fixture
    @staticmethod
    def transient_rdm() -> RocqDocManager:
        """A RocqDocManager for a fake file that can't be loaded."""
        return RDM_Tests.mk_rdm()

    @pytest.fixture
    @staticmethod
    def loadable_rdm() -> RocqDocManager:
        """A RocqDocManager for a real file that can be loaded."""
        return RDM_Tests.mk_rdm(path="./tests/test.v")

    @staticmethod
    def rocq_whitespace_strategy() -> st.SearchStrategy[str]:
        """Generates arbitrary sequences of Rocq whitespace characters."""
        # We use a limited, safe alphabet of standard whitespace characters.
        return st.text(
            alphabet='\n\t ',
            min_size=1,  # Must have at least one character to be a blank
            max_size=20,  # Keep the size reasonable for testing
        )

    @staticmethod
    def rocq_comment_strategy() -> st.SearchStrategy[str]:
        """Generates non-nested Coq comments (e.g., (* some text *))."""
        # Content of the comment: arbitrary text, excluding nested comment
        # delimiters '(*' and '*)'
        comment_content = st.text(
            st.characters(
                # Unicode character properties:
                # - [L]: letter
                # - [N]: number
                # - [P]: punctuation
                # - [Z]: separator
                whitelist_categories=('L', 'N', 'P', 'Z'),
                min_codepoint=32,
                max_codepoint=126
            ),
            max_size=15,
        )
        # Map the content into the (* ... *) wrapper
        return comment_content.map(lambda s: f"(* {s} *)")

    @staticmethod
    def rocq_blanks_strategy() -> st.SearchStrategy[str]:
        return st.one_of(
            RDM_Tests.rocq_whitespace_strategy(),
            RDM_Tests.rocq_comment_strategy()
        )

    @staticmethod
    def rocq_trivial_blank_cmd_sequence_strategy() -> st.SearchStrategy[
            list[tuple[str, bool]]
    ]:
        return st.lists(
            st.one_of(
                RDM_Tests.rocq_blanks_strategy().map(lambda s: (s, False)),
                st.just(("Check tt.", True))
            )
        )

    @contextmanager
    @staticmethod
    def assert_commands_inserted(
            rdm: RocqDocManager,
            cmds: list[str],
            ignore_blanks: bool = True,
            suffix_unchanged: bool = True,
    ) -> Iterator[RocqDocManager]:
        expected_prefix_extension = [
            RocqDocManager.PrefixItem(
                text=cmd,
                kind="command",
            ) for cmd in cmds
        ]

        doc_prefix = rdm.doc_prefix()
        doc_suffix = rdm.doc_suffix()

        yield rdm

        new_doc_prefix = rdm.doc_prefix()
        if ignore_blanks:
            new_doc_prefix = (
                new_doc_prefix[:len(doc_prefix)] +
                list(filter(
                    lambda item: item.kind == "command",
                    new_doc_prefix[len(doc_prefix):],
                ))
            )

        assert len(doc_prefix) + len(cmds) == len(new_doc_prefix)
        new_prefix_extension = new_doc_prefix[len(doc_prefix):]
        for i in range(len(cmds)):
            expected_item = expected_prefix_extension[i]
            new_item = new_prefix_extension[i]
            assert expected_item.text == new_item.text
            assert expected_item.kind == new_item.kind

        if suffix_unchanged:
            assert doc_suffix == rdm.doc_suffix()

    @contextmanager
    @staticmethod
    def assert_doc_unchanged(
            rdm: RocqDocManager
    ) -> Iterator[RocqDocManager]:
        doc_prefix = rdm.doc_prefix()
        doc_suffix = rdm.doc_suffix()
        yield rdm
        assert doc_prefix == rdm.doc_prefix()
        assert doc_suffix == rdm.doc_suffix()

    @staticmethod
    def assert_check_ok(
            rdm: RocqDocManager,
            term: str = "nat",
            lhs: str = "nat",
            rhs: str = "Set",
    ) -> None:
        query_reply = rdm.text_query_all(f"Check {term}.", indices=None)
        assert not isinstance(query_reply, RocqDocManager.Err)
        assert len(query_reply) == 1
        parts = [s.strip() for s in query_reply[0].split(":")]
        assert parts == [lhs, rhs]

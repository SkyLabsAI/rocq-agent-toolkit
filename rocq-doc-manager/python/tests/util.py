import os
from collections.abc import AsyncIterator, Iterator
from contextlib import asynccontextmanager, contextmanager
from typing import Any

import pytest
import pytest_asyncio
import rocq_doc_manager
from hypothesis import strategies as st
from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_doc_manager.rocq_doc_manager import AsyncRocqDocManager

LOADABLE_DOC = "./tests/test.v"
TRANSIENT_DOC = "my_fake.v"


# NOTE: The interaction of async and fixtures is quite complex, and,
# to make matters worse, fixtures are not type checked which means that
# we get a lot of runtime errors during tests.
class RDM_Tests:
    # NOTE: these are dynamically computed by code at the end of this file.
    TEST_DOT_V_DOC_LEN: int | None = None
    TEST_DOT_V_NO_THEOREM_PREFIX_LEN: int | None = None

    @classmethod
    def CONSTANT_NAMES(cls) -> list[str]:
        return [
            "TEST_DOT_V_DOC_LEN",
            "TEST_DOT_V_NO_THEOREM_PREFIX_LEN",
        ]

    @classmethod
    def CONSTANTS(cls) -> dict[str, Any | None]:
        return {nm: getattr(cls, nm, None) for nm in cls.CONSTANT_NAMES()}

    @staticmethod
    async def mk_rdm(
        path: str = "my_fake.v", rocq_args: list[str] | None = None
    ) -> AsyncRocqDocManager:
        return await rocq_doc_manager.create(
            path,
            rocq_args,
            dune=os.environ.get("RDM_USE_DUNE", "True") == "True",
        )

    @pytest_asyncio.fixture(scope="class")
    @staticmethod
    async def transient_shared_rdm() -> AsyncRocqDocManager:
        """A RocqCursor for a fake file that can't be loaded."""
        return await RDM_Tests.mk_rdm()

    @pytest_asyncio.fixture(scope="class")
    @staticmethod
    async def transient_shared_rc() -> RocqCursor:
        """A RocqCursor for a fake file that can't be loaded."""
        return (await RDM_Tests.mk_rdm()).cursor()

    @pytest_asyncio.fixture(scope="class")
    @staticmethod
    async def loaded_shared_rdm() -> AsyncRocqDocManager:
        """A RocqCursor for a real file that can be loaded."""
        rdm = await RDM_Tests.mk_rdm(path="./tests/test.v")
        assert not isinstance(
            await rdm.cursor().load_file(),
            rdm_api.Err,
        )
        return rdm

    @pytest_asyncio.fixture(scope="class")
    @staticmethod
    async def loaded_shared_rc() -> RocqCursor:
        """A RocqCursor for a real file that can be loaded."""
        rdm = await RDM_Tests.mk_rdm(path="./tests/test.v")
        assert not isinstance(
            await rdm.cursor().load_file(),
            rdm_api.Err,
        )
        return rdm.cursor()

    @asynccontextmanager
    @staticmethod
    async def starting_from(
        rdm: RocqCursor,
        /,
        idx: int,
    ) -> AsyncIterator[RocqCursor]:
        assert not isinstance(
            await rdm.go_to(idx),
            rdm_api.Err,
        )
        yield rdm

    @pytest_asyncio.fixture
    @staticmethod
    async def transient_rdm() -> AsyncRocqDocManager:
        """A RocqCursor for a fake file that can't be loaded."""
        return await RDM_Tests.mk_rdm()

    @pytest_asyncio.fixture
    @staticmethod
    async def transient_rc() -> RocqCursor:
        """A RocqCursor for a fake file that can't be loaded."""
        return (await RDM_Tests.mk_rdm()).cursor()

    @pytest_asyncio.fixture
    @staticmethod
    async def loadable_rdm() -> AsyncRocqDocManager:
        """A RocqCursor for a real file that can be loaded."""
        return await RDM_Tests.mk_rdm(path="./tests/test.v")

    @pytest_asyncio.fixture
    @staticmethod
    async def loadable_rc() -> RocqCursor:
        """A RocqCursor for a real file that can be loaded."""
        return (await RDM_Tests.mk_rdm(path="./tests/test.v")).cursor()

    @staticmethod
    def rocq_whitespace_strategy() -> st.SearchStrategy[str]:
        """Generates arbitrary sequences of Rocq whitespace characters."""
        # We use a limited, safe alphabet of standard whitespace characters.
        return st.text(
            alphabet="\n\t ",
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
                whitelist_categories=("L", "N", "P", "Z"),
                min_codepoint=32,
                max_codepoint=126,
            ),
            max_size=15,
        )
        # Map the content into the (* ... *) wrapper
        return comment_content.map(lambda s: f"(* {s} *)")

    @staticmethod
    def rocq_blanks_strategy() -> st.SearchStrategy[str]:
        return st.one_of(
            RDM_Tests.rocq_whitespace_strategy(), RDM_Tests.rocq_comment_strategy()
        )

    @staticmethod
    def rocq_trivial_blank_cmd_sequence_strategy() -> st.SearchStrategy[
        list[tuple[str, bool]]
    ]:
        return st.lists(
            st.one_of(
                RDM_Tests.rocq_blanks_strategy().map(lambda s: (s, False)),
                st.just(("Check tt.", True)),
            )
        )

    @asynccontextmanager
    @staticmethod
    async def assert_commands_inserted(
        rdm: RocqCursor,
        cmds: list[str],
        ignore_blanks: bool = True,
        suffix_unchanged: bool = True,
    ) -> AsyncIterator[RocqCursor]:
        expected_prefix_extension = [
            rdm_api.PrefixItem(
                text=cmd,
                offset=0,
                kind="command",
            )
            for cmd in cmds
        ]

        doc_prefix = await rdm.doc_prefix()
        doc_suffix = await rdm.doc_suffix()

        yield rdm

        new_doc_prefix = await rdm.doc_prefix()
        if ignore_blanks:
            new_doc_prefix = new_doc_prefix[: len(doc_prefix)] + list(
                filter(
                    lambda item: item.kind == "command",
                    new_doc_prefix[len(doc_prefix) :],
                )
            )

        assert len(doc_prefix) + len(cmds) == len(new_doc_prefix)
        new_prefix_extension = new_doc_prefix[len(doc_prefix) :]
        for i in range(len(cmds)):
            expected_item = expected_prefix_extension[i]
            new_item = new_prefix_extension[i]
            assert expected_item.text == new_item.text
            assert expected_item.kind == new_item.kind

        if suffix_unchanged:
            assert doc_suffix == await rdm.doc_suffix()

    @asynccontextmanager
    @staticmethod
    async def assert_doc_unchanged(rdm: RocqCursor) -> AsyncIterator[RocqCursor]:
        doc_prefix = await rdm.doc_prefix()
        doc_suffix = await rdm.doc_suffix()
        yield rdm
        assert doc_prefix == await rdm.doc_prefix()
        assert doc_suffix == await rdm.doc_suffix()

    @staticmethod
    async def assert_check_ok(
        rdm: RocqCursor,
        term: str = "nat",
        lhs: str = "nat",
        rhs: str = "Set",
    ) -> None:
        query_reply = await rdm.query_text_all(f"Check {term}.", indices=None)
        assert not isinstance(query_reply, rdm_api.Err)
        assert len(query_reply) == 1
        parts = [s.strip() for s in query_reply[0].split(":")]
        assert parts == [lhs, rhs]


@pytest.mark.asyncio
async def test_something() -> None:
    async with (await RDM_Tests.mk_rdm("./tests/test.v")).sess() as rdm:
        doc_contents = await rdm.cursor().doc_suffix()

        RDM_Tests.TEST_DOT_V_DOC_LEN = len(doc_contents)

        idx = 0
        for item in doc_contents:
            if item.kind == "blanks" or not item.text.startswith("Theorem"):
                idx += 1
            else:
                break
        RDM_Tests.TEST_DOT_V_NO_THEOREM_PREFIX_LEN = idx

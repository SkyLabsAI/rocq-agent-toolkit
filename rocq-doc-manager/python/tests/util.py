from contextlib import contextmanager
import os
import pytest
from typing import Iterator

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

    @pytest.fixture
    @classmethod
    def transient_rdm(cls) -> RocqDocManager:
        """A RocqDocManager for a fake file that can't be loaded."""
        return cls.mk_rdm()

    @pytest.fixture
    @classmethod
    def loadable_rdm(cls) -> RocqDocManager:
        """A RocqDocManager for a real file that can be loaded."""
        return cls.mk_rdm(path="./tests/test.v")

    @contextmanager
    def assert_commands_inserted(
            self,
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
    def assert_doc_unchanged(
            self,
            rdm: RocqDocManager
    ) -> Iterator[RocqDocManager]:
        doc_prefix = rdm.doc_prefix()
        doc_suffix = rdm.doc_suffix()
        yield rdm
        assert doc_prefix == rdm.doc_prefix()
        assert doc_suffix == rdm.doc_suffix()

    def assert_check_ok(
            self,
            rdm: RocqDocManager,
            term: str = "nat",
            lhs: str = "nat",
            rhs: str = "Set",
    ) -> None:
        query_reply = rdm.text_query_all(f"Check {term}.", indices=None)
        assert not isinstance(query_reply, RocqDocManager.Err)
        assert len(query_reply) == 1
        parts = list(map(lambda s: s.strip(), query_reply[0].split(":")))
        assert parts == [lhs, rhs]

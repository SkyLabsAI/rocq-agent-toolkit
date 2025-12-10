import logging
from pathlib import Path

import pytest
from rocq_doc_manager import RocqDocManager, RocqCursor
from rocq_doc_manager.rocq_cursor_protocol import RocqCursorProtocol
from rocq_doc_manager.rocq_doc_manager_api import RocqDocManagerAPI

from .util import RDM_Tests


class Test_API(RDM_Tests):
    def test_load_file(self, loadable_rdm: RocqCursor) -> None:
        assert loadable_rdm.load_file() is None

        result = loadable_rdm.doc_suffix()
        assert result == [
            RocqCursor.SuffixItem(**kwargs)
            for kwargs in [
                {"kind": "command", "text": "Require Import Stdlib.ZArith.BinInt."},
                {"kind": "blanks", "text": "\n\n"},
                {"kind": "command", "text": "About nil."},
                {"kind": "blanks", "text": "\n    "},
                {"kind": "command", "text": "Definition junk :=\n\n\nnat."},
                {"kind": "blanks", "text": "\n"},
                {"kind": "command", "text": "Check 12 < 42 <= 100."},
                {"kind": "blanks", "text": "\n\n\n"},
                {"kind": "command", "text": "Theorem test : forall x : nat, x = x."},
                {"kind": "blanks", "text": "\n"},
                {"kind": "command", "text": "Proof."},
                {"kind": "blanks", "text": "\n  "},
                {"kind": "command", "text": "intro x."},
                {"kind": "blanks", "text": "\n  "},
                {"kind": "command", "text": "reflexivity."},
                {"kind": "blanks", "text": "\n"},
                {"kind": "command", "text": "Qed."},
            ]
        ]

    def test_Check_query_text(
        self,
        transient_rdm: RocqCursor,
    ) -> None:
        check_reply = transient_rdm.query_text("Check nat.", 0)
        assert not isinstance(check_reply, RocqCursor.Err)
        assert check_reply == "nat\n     : Set"

    def test_doc_suffix(
        self,
        loadable_rdm: RocqCursor,
    ) -> None:
        with loadable_rdm.sess() as rdm:
            assert rdm.doc_suffix() == [
                RocqCursor.SuffixItem(
                    text="Require Import Stdlib.ZArith.BinInt.",
                    kind="command",
                ),
                RocqCursor.SuffixItem(
                    text="\n\n",
                    kind="blanks",
                ),
                RocqCursor.SuffixItem(
                    text="About nil.",
                    kind="command",
                ),
                RocqCursor.SuffixItem(
                    text="\n    ",
                    kind="blanks",
                ),
                RocqCursor.SuffixItem(
                    text="Definition junk :=\n\n\nnat.",
                    kind="command",
                ),
                RocqCursor.SuffixItem(
                    text="\n",
                    kind="blanks",
                ),
                RocqCursor.SuffixItem(
                    text="Check 12 < 42 <= 100.",
                    kind="command",
                ),
                RocqCursor.SuffixItem(
                    text="\n\n\n",
                    kind="blanks",
                ),
                RocqCursor.SuffixItem(
                    text="Theorem test : forall x : nat, x = x.",
                    kind="command",
                ),
                RocqCursor.SuffixItem(
                    text="\n",
                    kind="blanks",
                ),
                RocqCursor.SuffixItem(
                    text="Proof.",
                    kind="command",
                ),
                RocqCursor.SuffixItem(
                    text="\n  ",
                    kind="blanks",
                ),
                RocqCursor.SuffixItem(
                    text="intro x.",
                    kind="command",
                ),
                RocqCursor.SuffixItem(
                    text="\n  ",
                    kind="blanks",
                ),
                RocqCursor.SuffixItem(
                    text="reflexivity.",
                    kind="command",
                ),
                RocqCursor.SuffixItem(
                    text="\n",
                    kind="blanks",
                ),
                RocqCursor.SuffixItem(
                    text="Qed.",
                    kind="command",
                ),
            ]

    def test_run_command_tac_fail(
        self,
        transient_rdm: RocqCursor,
    ) -> None:
        with transient_rdm.aborted_goal_ctx(goal="False"):
            fail_tac_reply = transient_rdm.run_command("solve [auto].")
            assert isinstance(fail_tac_reply, RocqCursor.Err)
            assert fail_tac_reply.message == "No applicable tactic."

    def _test_API_PATCH_insert_commands_without_intervening_blanks(
        self,
        tmp_path: Path,
        /,
        rdm_cls: type[RocqCursor],
        should_succeed: bool,
    ) -> None:
        tmp_v = tmp_path / "foo.v"
        tmp_rdm = RDM_Tests.mk_rdm(path=str(tmp_v))
        with tmp_rdm.sess(load_file=False):
            rc = tmp_rdm.cursor()
            assert not isinstance(
                rdm_cls.insert_command(rc, "Check tt."),
                rdm_cls.Err,
            )
            # NOTE: no intervening blank
            assert not isinstance(
                rdm_cls.insert_command(rc, "Check tt."),
                rdm_cls.Err,
            )
            rdm_cls.commit(rc, True)
            compile_result = rdm_cls.compile(rc)
            if should_succeed:
                assert compile_result.error is None
            else:
                assert compile_result.error is not None

    def test_insert_commands_without_intervening_blanks_fails(
        self,
        tmp_path: Path,
    ) -> None:
        self._test_API_PATCH_insert_commands_without_intervening_blanks(
            tmp_path,
            rdm_cls=RocqCursor,
            should_succeed=False,
        )

    def test_patched_insert_commands_without_intervening_blanks_works(
        self,
        tmp_path: Path,
    ) -> None:
        self._test_API_PATCH_insert_commands_without_intervening_blanks(
            tmp_path,
            rdm_cls=RocqCursor,
            should_succeed=True,
        )

    def _test_API_PATCH_double_load_file(
        self,
        caplog: pytest.LogCaptureFixture,
        loadable_rdm: RocqCursor,
        /,
        rdm_cls: type[RocqCursorProtocol],
        duplicates_doc_content: bool,
    ) -> None:
        with caplog.at_level(logging.WARNING):
            assert not isinstance(
                rdm_cls.load_file(loadable_rdm),
                rdm_cls.Err,
            )
            suffix = loadable_rdm.doc_suffix()
            assert not isinstance(
                rdm_cls.load_file(loadable_rdm),
                rdm_cls.Err,
            )
            if duplicates_doc_content:
                assert loadable_rdm.doc_suffix() == suffix * 2
                assert not caplog.text
            else:
                assert loadable_rdm.doc_suffix() == suffix
                assert "duplicates document content" in caplog.text

    def test_double_load_file_duplicates_doc_content(
        self,
        caplog: pytest.LogCaptureFixture,
        loadable_rdm: RocqCursor,
    ) -> None:
        return self._test_API_PATCH_double_load_file(
            caplog,
            loadable_rdm,
            rdm_cls=RocqCursor,
            duplicates_doc_content=True,
        )

    def test_patched_double_load_file_(
        self,
        caplog: pytest.LogCaptureFixture,
        loadable_rdm: RocqCursor,
    ) -> None:
        return self._test_API_PATCH_double_load_file(
            caplog,
            loadable_rdm,
            rdm_cls=RocqCursor,
            duplicates_doc_content=True,
        )

import logging
from pathlib import Path

import pytest
from rocq_doc_manager import RocqCursor, RocqDocManager
from rocq_doc_manager.rocq_cursor_protocol import RocqCursorProtocol

from .util import RDM_Tests


class Test_API(RDM_Tests):
    def test_load_file(self, loadable_rdm: RocqDocManager) -> None:
        rc = loadable_rdm.cursor()
        assert rc.load_file() is None

        result = rc.doc_suffix()
        assert result == [
            RocqCursor.SuffixItem(
                kind="command", text="Require Import Stdlib.ZArith.BinInt."
            ),
            RocqCursor.SuffixItem(kind="blanks", text="\n\n"),
            RocqCursor.SuffixItem(kind="command", text="About nil."),
            RocqCursor.SuffixItem(kind="blanks", text="\n    "),
            RocqCursor.SuffixItem(kind="command", text="Definition junk :=\n\n\nnat."),
            RocqCursor.SuffixItem(kind="blanks", text="\n"),
            RocqCursor.SuffixItem(kind="command", text="Check 12 < 42 <= 100."),
            RocqCursor.SuffixItem(kind="blanks", text="\n\n\n"),
            RocqCursor.SuffixItem(
                kind="command", text="Theorem test : forall x : nat, x = x."
            ),
            RocqCursor.SuffixItem(kind="blanks", text="\n"),
            RocqCursor.SuffixItem(kind="command", text="Proof."),
            RocqCursor.SuffixItem(kind="blanks", text="\n  "),
            RocqCursor.SuffixItem(kind="command", text="intro x."),
            RocqCursor.SuffixItem(kind="blanks", text="\n  "),
            RocqCursor.SuffixItem(kind="command", text="reflexivity."),
            RocqCursor.SuffixItem(kind="blanks", text="\n"),
            RocqCursor.SuffixItem(kind="command", text="Qed."),
        ]

    def test_Check_query_text(
        self,
        transient_rdm: RocqDocManager,
    ) -> None:
        rc = transient_rdm.cursor()
        check_reply = rc.query_text("Check nat.", 0)
        assert not isinstance(check_reply, RocqCursor.Err)
        assert check_reply == "nat\n     : Set"

    def test_doc_suffix(
        self,
        loadable_rdm: RocqDocManager,
    ) -> None:
        with loadable_rdm.sess() as rdm:
            rc = rdm.cursor()
            assert rc.doc_suffix() == [
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
        transient_rdm: RocqDocManager,
    ) -> None:
        rc = transient_rdm.cursor()
        with rc.aborted_goal_ctx(goal="False"):
            fail_tac_reply = rc.run_command("solve [auto].")
            assert isinstance(fail_tac_reply, RocqCursor.Err)
            assert fail_tac_reply.message == "No applicable tactic."

    def _test_API_PATCH_insert_commands_without_intervening_blanks(
        self,
        tmp_path: Path,
        /,
        rc_cls: type[RocqCursor],
        should_succeed: bool,
    ) -> None:
        tmp_v = tmp_path / "foo.v"
        tmp_rdm = RDM_Tests.mk_rdm(path=str(tmp_v))
        with tmp_rdm.sess(load_file=False):
            rc = tmp_rdm.cursor()
            assert not isinstance(
                rc_cls.insert_command(rc, "Check tt."),
                rc_cls.Err,
            )
            # NOTE: no intervening blank
            assert not isinstance(
                rc_cls.insert_command(rc, "Check tt."),
                rc_cls.Err,
            )
            rc_cls.commit(rc, None, include_suffix=True)
            compile_result = rc_cls.compile(rc)
            if should_succeed:
                assert compile_result.error is None
            else:
                assert compile_result.error is not None

    # def test_insert_commands_without_intervening_blanks_fails(
    #     self,
    #     tmp_path: Path,
    # ) -> None:
    #     self._test_API_PATCH_insert_commands_without_intervening_blanks(
    #         tmp_path,
    #         rc_cls=RocqCursor,
    #         should_succeed=False,
    #     )

    def test_patched_insert_commands_without_intervening_blanks_works(
        self,
        tmp_path: Path,
    ) -> None:
        self._test_API_PATCH_insert_commands_without_intervening_blanks(
            tmp_path,
            rc_cls=RocqCursor,
            should_succeed=True,
        )

    def _test_API_PATCH_double_load_file(
        self,
        caplog: pytest.LogCaptureFixture,
        loadable_rdm: RocqDocManager,
        /,
        rc_cls: type[RocqCursorProtocol],
        duplicates_doc_content: bool,
    ) -> None:
        rc = loadable_rdm.cursor()
        with caplog.at_level(logging.WARNING):
            assert not isinstance(
                rc_cls.load_file(rc),
                rc_cls.Err,
            )
            suffix = rc.doc_suffix()
            assert not isinstance(
                rc_cls.load_file(rc),
                rc_cls.Err,
            )
            if duplicates_doc_content:
                assert rc.doc_suffix() == suffix * 2
                assert not caplog.text
            else:
                assert rc.doc_suffix() == suffix
                assert "duplicates document content" in caplog.text

    def test_double_load_file_duplicates_doc_content(
        self,
        caplog: pytest.LogCaptureFixture,
        loadable_rdm: RocqDocManager,
    ) -> None:
        return self._test_API_PATCH_double_load_file(
            caplog,
            loadable_rdm,
            rc_cls=RocqCursor,
            duplicates_doc_content=True,
        )

    def test_patched_double_load_file_(
        self,
        caplog: pytest.LogCaptureFixture,
        loadable_rdm: RocqDocManager,
    ) -> None:
        return self._test_API_PATCH_double_load_file(
            caplog,
            loadable_rdm,
            rc_cls=RocqCursor,
            duplicates_doc_content=True,
        )

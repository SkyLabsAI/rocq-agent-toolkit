import logging
from pathlib import Path

import pytest

from rocq_doc_manager import RocqDocManager
from rocq_doc_manager.rocq_doc_manager_api import RocqDocManagerAPI

from .util import RDM_Tests


class Test_API(RDM_Tests):
    @pytest.mark.parametrize('rdm_fixture', ['loadable_rdm', 'transient_rdm'])
    def test_non_existant(
            self,
            rdm_fixture: str,
            request: pytest.FixtureRequest,
    ) -> None:
        rdm = request.getfixturevalue(rdm_fixture)
        result = rdm.raw_request("non-existant", [])
        assert isinstance(result, RocqDocManager.Err)
        assert result == RocqDocManager.Err("Method non-existant not found.", data=None)

    def test_load_file(self, loadable_rdm: RocqDocManager) -> None:
        result = loadable_rdm.raw_request("load_file", [])
        assert isinstance(result, RocqDocManager.Resp)
        assert result == RocqDocManager.Resp(None)

        result = loadable_rdm.raw_request("doc_suffix", [])
        assert isinstance(result, RocqDocManager.Resp)
        assert result == RocqDocManager.Resp([{'kind': "command", 'text': "Require Import Stdlib.ZArith.BinInt."}, {'kind': 'blanks', 'text': '\n\n'}, {'kind': 'command', 'text': 'About nil.'}, {'kind': 'blanks', 'text': '\n    '}, {'kind': 'command', 'text': 'Definition junk :=\n\n\nnat.'}, {'kind': 'blanks', 'text': '\n'}, {'kind': 'command', 'text': 'Check 12 < 42 <= 100.'}, {'kind': 'blanks', 'text': '\n\n\n'}, {'kind': 'command', 'text': 'Theorem test : forall x : nat, x = x.'}, {'kind': 'blanks', 'text': '\n'}, {'kind': 'command', 'text': 'Proof.'}, {'kind': 'blanks', 'text': '\n  '}, {'kind': 'command', 'text': 'intro x.'}, {'kind': 'blanks', 'text': '\n  '}, {'kind': 'command', 'text': 'reflexivity.'}, {'kind': 'blanks', 'text': '\n'}, {'kind': 'command', 'text': 'Qed.'}])

    def test_Check_query_text(
            self,
            transient_rdm: RocqDocManager,
    ) -> None:
        check_reply = transient_rdm.query_text("Check nat.", 0)
        assert not isinstance(check_reply, RocqDocManager.Err)
        assert check_reply == "nat\n     : Set"

    def test_doc_suffix(
            self,
            loadable_rdm: RocqDocManager,
    ) -> None:
        with loadable_rdm.sess() as rdm:
            assert rdm.doc_suffix() == [
                RocqDocManager.SuffixItem(
                    text='Require Import Stdlib.ZArith.BinInt.',
                    kind='command',
                ),
                RocqDocManager.SuffixItem(
                    text='\n'
                         '\n',
                    kind='blanks',
                ),
                RocqDocManager.SuffixItem(
                    text='About nil.',
                    kind='command',
                ),
                RocqDocManager.SuffixItem(
                    text='\n'
                         '    ',
                    kind='blanks',
                ),
                RocqDocManager.SuffixItem(
                    text='Definition junk :=\n'
                         '\n'
                         '\n'
                         'nat.',
                    kind='command',
                ),
                RocqDocManager.SuffixItem(
                    text='\n',
                    kind='blanks',
                ),
                RocqDocManager.SuffixItem(
                    text='Check 12 < 42 <= 100.',
                    kind='command',
                ),
                RocqDocManager.SuffixItem(
                    text='\n'
                         '\n'
                         '\n',
                    kind='blanks',
                ),
                RocqDocManager.SuffixItem(
                    text='Theorem test : forall x : nat, x = x.',
                    kind='command',
                ),
                RocqDocManager.SuffixItem(
                    text='\n',
                    kind='blanks',
                ),
                RocqDocManager.SuffixItem(
                    text='Proof.',
                    kind='command',
                ),
                RocqDocManager.SuffixItem(
                    text='\n'
                         '  ',
                    kind='blanks',
                ),
                RocqDocManager.SuffixItem(
                    text='intro x.',
                    kind='command',
                ),
                RocqDocManager.SuffixItem(
                    text='\n'
                         '  ',
                    kind='blanks',
                ),
                RocqDocManager.SuffixItem(
                    text='reflexivity.',
                    kind='command',
                ),
                RocqDocManager.SuffixItem(
                    text='\n',
                    kind='blanks',
                ),
                RocqDocManager.SuffixItem(
                    text='Qed.',
                    kind='command',
                ),
            ]

    def test_run_command_tac_fail(
            self,
            transient_rdm: RocqDocManager,
    ) -> None:
        with transient_rdm.aborted_goal_ctx(goal="False"):
            fail_tac_reply = transient_rdm.run_command("solve [auto].")
            assert isinstance(fail_tac_reply, RocqDocManager.Err)
            assert fail_tac_reply.message == "No applicable tactic."

    def _test_API_PATCH_insert_commands_without_intervening_blanks(
            self,
            tmp_path: Path,
            /,
            rdm_cls: type[RocqDocManagerAPI],
            should_succeed: bool,
    ) -> None:
        tmp_v = tmp_path / "foo.v"
        tmp_rdm = RDM_Tests.mk_rdm(path=str(tmp_v))
        with tmp_rdm.sess(load_file=False):
            assert not isinstance(
                rdm_cls.insert_command(tmp_rdm, "Check tt."),
                rdm_cls.Err,
            )
            # NOTE: no intervening blank
            assert not isinstance(
                rdm_cls.insert_command(tmp_rdm, "Check tt."),
                rdm_cls.Err,
            )
            rdm_cls.commit(tmp_rdm, True)
            compile_result = rdm_cls.compile(tmp_rdm)
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
            rdm_cls=RocqDocManagerAPI,
            should_succeed=False,
        )

    def test_patched_insert_commands_without_intervening_blanks_works(
            self,
            tmp_path: Path,
    ) -> None:
        self._test_API_PATCH_insert_commands_without_intervening_blanks(
            tmp_path,
            rdm_cls=RocqDocManager,
            should_succeed=True,
        )

    def _test_API_PATCH_double_load_file(
            self,
            caplog: pytest.LogCaptureFixture,
            loadable_rdm: RocqDocManager,
            /,
            rdm_cls: type[RocqDocManagerAPI],
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
            loadable_rdm: RocqDocManager,
    ) -> None:
        return self._test_API_PATCH_double_load_file(
            caplog,
            loadable_rdm,
            rdm_cls=RocqDocManagerAPI,
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
            rdm_cls=RocqDocManagerAPI,
            duplicates_doc_content=True,
        )

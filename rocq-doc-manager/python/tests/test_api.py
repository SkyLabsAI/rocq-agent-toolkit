from pathlib import Path

import pytest
from rocq_doc_manager import AsyncRocqDocManager, RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_doc_manager.rocq_cursor import RDMRocqCursor

from .util import RDM_Tests


@pytest.mark.asyncio(loop_scope="class")
class Test_API(RDM_Tests):
    async def test_load_file(self, loadable_rdm: AsyncRocqDocManager) -> None:
        rc = loadable_rdm.cursor()
        assert await rc.load_file() is None

        result = await rc.doc_suffix()
        assert result == [
            rdm_api.SuffixItem(
                kind="command", text="Require Import Stdlib.ZArith.BinInt."
            ),
            rdm_api.SuffixItem(kind="blanks", text="\n\n"),
            rdm_api.SuffixItem(kind="command", text="About nil."),
            rdm_api.SuffixItem(kind="blanks", text="\n    "),
            rdm_api.SuffixItem(kind="command", text="Definition junk :=\n\n\nnat."),
            rdm_api.SuffixItem(kind="blanks", text="\n"),
            rdm_api.SuffixItem(kind="command", text="Check 12 < 42 <= 100."),
            rdm_api.SuffixItem(kind="blanks", text="\n\n\n"),
            rdm_api.SuffixItem(
                kind="command", text="Theorem test : forall x : nat, x = x."
            ),
            rdm_api.SuffixItem(kind="blanks", text="\n"),
            rdm_api.SuffixItem(kind="command", text="Proof."),
            rdm_api.SuffixItem(kind="blanks", text="\n  "),
            rdm_api.SuffixItem(kind="command", text="intro x."),
            rdm_api.SuffixItem(kind="blanks", text="\n  "),
            rdm_api.SuffixItem(kind="command", text="reflexivity."),
            rdm_api.SuffixItem(kind="blanks", text="\n"),
            rdm_api.SuffixItem(kind="command", text="Qed."),
        ]

    async def test_Check_query_text(
        self,
        transient_rdm: AsyncRocqDocManager,
    ) -> None:
        rc = transient_rdm.cursor()
        check_reply = await rc.query_text("Check nat.", index=0)
        assert not isinstance(check_reply, rdm_api.Err)
        assert check_reply == "nat\n     : Set"

    async def test_doc_suffix(
        self,
        loadable_rdm: AsyncRocqDocManager,
    ) -> None:
        async with loadable_rdm.sess() as rdm:
            rc = rdm.cursor()
            assert await rc.doc_suffix() == [
                rdm_api.SuffixItem(
                    text="Require Import Stdlib.ZArith.BinInt.",
                    kind="command",
                ),
                rdm_api.SuffixItem(
                    text="\n\n",
                    kind="blanks",
                ),
                rdm_api.SuffixItem(
                    text="About nil.",
                    kind="command",
                ),
                rdm_api.SuffixItem(
                    text="\n    ",
                    kind="blanks",
                ),
                rdm_api.SuffixItem(
                    text="Definition junk :=\n\n\nnat.",
                    kind="command",
                ),
                rdm_api.SuffixItem(
                    text="\n",
                    kind="blanks",
                ),
                rdm_api.SuffixItem(
                    text="Check 12 < 42 <= 100.",
                    kind="command",
                ),
                rdm_api.SuffixItem(
                    text="\n\n\n",
                    kind="blanks",
                ),
                rdm_api.SuffixItem(
                    text="Theorem test : forall x : nat, x = x.",
                    kind="command",
                ),
                rdm_api.SuffixItem(
                    text="\n",
                    kind="blanks",
                ),
                rdm_api.SuffixItem(
                    text="Proof.",
                    kind="command",
                ),
                rdm_api.SuffixItem(
                    text="\n  ",
                    kind="blanks",
                ),
                rdm_api.SuffixItem(
                    text="intro x.",
                    kind="command",
                ),
                rdm_api.SuffixItem(
                    text="\n  ",
                    kind="blanks",
                ),
                rdm_api.SuffixItem(
                    text="reflexivity.",
                    kind="command",
                ),
                rdm_api.SuffixItem(
                    text="\n",
                    kind="blanks",
                ),
                rdm_api.SuffixItem(
                    text="Qed.",
                    kind="command",
                ),
            ]

    async def test_run_command_tac_fail(
        self,
        transient_rdm: AsyncRocqDocManager,
    ) -> None:
        rc = transient_rdm.cursor()
        async with rc.aborted_goal_ctx(goal="False"):
            fail_tac_reply = await rc.run_command("solve [auto].")
            assert isinstance(fail_tac_reply, rdm_api.Err)
            assert fail_tac_reply.message == "No applicable tactic."

    async def _test_API_PATCH_insert_commands_without_intervening_blanks(
        self,
        tmp_path: Path,
        /,
        rc_cls: type[RocqCursor],
        should_succeed: bool,
    ) -> None:
        tmp_v = tmp_path / "foo.v"
        tmp_rdm = await RDM_Tests.mk_rdm(path=str(tmp_v))
        async with tmp_rdm.sess(load_file=False):
            rc = tmp_rdm.cursor()
            assert not isinstance(
                await rc_cls.insert_command(rc, "Check tt."),
                rdm_api.Err,
            )
            # NOTE: no intervening blank
            assert not isinstance(
                await rc_cls.insert_command(rc, "Check tt."),
                rdm_api.Err,
            )
            await rc_cls.commit(rc, None, include_suffix=True)
            compile_result = await rc_cls.compile(rc)
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

    async def test_patched_insert_commands_without_intervening_blanks_works(
        self,
        tmp_path: Path,
    ) -> None:
        await self._test_API_PATCH_insert_commands_without_intervening_blanks(
            tmp_path,
            rc_cls=RDMRocqCursor,
            should_succeed=True,
        )

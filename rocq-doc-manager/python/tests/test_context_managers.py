import itertools

import pytest
from hypothesis import given, settings
from rocq_doc_manager import RocqCursor, RocqDocManager
from rocq_doc_manager import rocq_doc_manager_api as api

from .util import RDM_Tests


class Test_RDM_sess(RDM_Tests):
    @pytest.mark.parametrize("rdm_fixture", ["loadable_rc", "transient_rc"])
    def test_sess_no_load(
        self,
        rdm_fixture: str,
        request: pytest.FixtureRequest,
    ) -> None:
        rdm: RocqCursor = request.getfixturevalue(rdm_fixture)
        with rdm.sess():
            RDM_Tests.assert_check_ok(rdm)

    def test_sess_load(self, loadable_rdm: RocqDocManager) -> None:
        with loadable_rdm.sess():
            rc = loadable_rdm.cursor()
            assert not isinstance(rc.run_step(), api.Resp)
            RDM_Tests.assert_check_ok(rc, term="N", lhs="N")

    def test_sess_load_nonexistent(self, transient_rdm: RocqDocManager) -> None:
        with pytest.raises(api.Error) as exc_info:
            with transient_rdm.sess():
                pass
        assert exc_info.match("my_fake.v: No such file or directory")


class Test_RDM_ctx(RDM_Tests):
    @pytest.mark.parametrize(
        "rdm_fixture, rollback",
        itertools.product(["loadable_rc", "transient_rc"], [True, False]),
    )
    def test_side_effects(
        self, rdm_fixture: str, rollback: bool, request: pytest.FixtureRequest
    ) -> None:
        rc: RocqCursor = request.getfixturevalue(rdm_fixture)
        cmds = [f"Compute ({i}+{i})." for i in range(100)]

        with (
            RDM_Tests.assert_doc_unchanged(rc)
            if rollback
            else RDM_Tests.assert_commands_inserted(rc, cmds=cmds)
        ):
            with rc.ctx(rollback=rollback):
                with RDM_Tests.assert_commands_inserted(rc, cmds=cmds):
                    for cmd in cmds:
                        assert not isinstance(rc.insert_command(cmd), api.Err)

    @given(
        prefix=RDM_Tests.rocq_trivial_blank_cmd_sequence_strategy(),
        rollback=RDM_Tests.rocq_trivial_blank_cmd_sequence_strategy(),
        suffix=RDM_Tests.rocq_trivial_blank_cmd_sequence_strategy(),
    )
    @settings(deadline=None)
    def test_property_rollback_ignores_blanks(
        self,
        transient_shared_rc: RocqCursor,
        prefix: list[tuple[str, bool]],
        rollback: list[tuple[str, bool]],
        suffix: list[tuple[str, bool]],
    ) -> None:
        def _process(items: list[tuple[str, bool]]) -> None:
            for text, is_cmd in items:
                if is_cmd:
                    assert not isinstance(
                        transient_shared_rc.insert_command(text), api.Err
                    )
                else:
                    transient_shared_rc.insert_blanks(text)

        # Set up the document to contain a suffix and prefix of interleaved
        # blanks/commands
        _process(suffix)
        transient_shared_rc.revert_before(False, 0)
        _process(prefix)

        with RDM_Tests.assert_doc_unchanged(transient_shared_rc):
            with transient_shared_rc.ctx(rollback=True):
                _process(rollback)


class Test_RDM_aborted_goal_ctx(RDM_Tests):
    @pytest.mark.parametrize("rollback", [True, False])
    def test_side_effects(
        self,
        transient_rdm: RocqDocManager,
        rollback: bool,
    ) -> None:
        rc = transient_rdm.cursor()
        goal = "True /\\ 1 = 1"
        proof_goal = "\n============================\n" + goal
        tac = "intuition auto."
        cmds = [
            f"Goal {goal}.",
            tac,
            "Abort.",
        ]
        with (
            RDM_Tests.assert_doc_unchanged(rc)
            if rollback
            else RDM_Tests.assert_commands_inserted(rc, cmds=cmds)
        ):
            with rc.aborted_goal_ctx(goal=goal, rollback=rollback):
                idtac_reply = rc.run_command("idtac.")
                assert isinstance(idtac_reply, api.CommandData)
                assert idtac_reply.proof_state is not None
                assert idtac_reply.proof_state.focused_goals == [proof_goal]

                tac_reply = rc.insert_command(tac)
                assert isinstance(tac_reply, api.CommandData)
                assert tac_reply.proof_state is not None
                assert tac_reply.proof_state.focused_goals == []
                assert tac_reply.proof_state.shelved_goals == 0
                assert tac_reply.proof_state.given_up_goals == 0
                assert tac_reply.proof_state.unfocused_goals == []


class Test_RDM_Section(RDM_Tests):
    def test_Context(self, transient_rdm: RocqDocManager) -> None:
        rc = transient_rdm.cursor()
        with RDM_Tests.assert_doc_unchanged(rc):
            context = [
                ("n", "nat"),
                ("b", "bool"),
                ("Hnb", "if b then n = 1 else n = 0"),
            ]
            with rc.Section(
                "test",
                context=[f"({ident} : {ty})" for ident, ty in context],
                rollback=True,
            ):
                for ident, ty in context:
                    RDM_Tests.assert_check_ok(
                        rc,
                        term=ident,
                        lhs=ident,
                        rhs=ty,
                    )

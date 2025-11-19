import itertools
import pytest
from hypothesis import given, settings, strategies as st

from rocq_doc_manager import RocqDocManager
from .util import RDM_Tests


class Test_RDM_sess(RDM_Tests):
    @pytest.mark.parametrize('rdm_fixture', ['loadable_rdm', 'transient_rdm'])
    def test_sess_no_load(
            self,
            rdm_fixture: str,
            request: pytest.FixtureRequest,
    ) -> None:
        rdm = request.getfixturevalue(rdm_fixture)
        with rdm.sess(load_file=False):
            RDM_Tests.assert_check_ok(rdm)

    def test_sess_load(self, loadable_rdm: RocqDocManager) -> None:
        with loadable_rdm.sess():
            assert not isinstance(loadable_rdm.run_step(), RocqDocManager.Resp)
            RDM_Tests.assert_check_ok(loadable_rdm, term="N", lhs="N")

    def test_sess_load_nonexistent(
            self,
            transient_rdm: RocqDocManager
    ) -> None:
        with pytest.raises(RocqDocManager.Error) as exc_info:
            with transient_rdm.sess():
                pass
        assert exc_info.match("my_fake.v: No such file or directory")


class Test_RDM_ctx(RDM_Tests):
    @pytest.mark.parametrize(
        'rdm_fixture, rollback',
        itertools.product(['loadable_rdm', 'transient_rdm'], [True, False])
    )
    def test_side_effects(
            self,
            rdm_fixture: str,
            rollback: bool,
            request: pytest.FixtureRequest
    ) -> None:
        rdm = request.getfixturevalue(rdm_fixture)
        print(rdm)
        cmds = [f"Compute ({i}+{i})." for i in range(100)]

        with (
                RDM_Tests.assert_doc_unchanged(rdm)
                if rollback else
                RDM_Tests.assert_commands_inserted(rdm, cmds=cmds)
        ):
            with rdm.ctx(rollback=rollback):
                with RDM_Tests.assert_commands_inserted(rdm, cmds=cmds):
                    for cmd in cmds:
                        assert not isinstance(
                            rdm.insert_command(cmd),
                            RocqDocManager.Err
                        )

    @given(
        prefix=RDM_Tests.rocq_trivial_blank_cmd_sequence_strategy(),
        rollback=RDM_Tests.rocq_trivial_blank_cmd_sequence_strategy(),
        suffix=RDM_Tests.rocq_trivial_blank_cmd_sequence_strategy(),
    )
    @settings(deadline=None)
    def test_property_rollback_ignores_blanks(
            self,
            transient_shared_rdm: RocqDocManager,
            prefix: list[tuple[str, bool]],
            rollback: list[tuple[str, bool]],
            suffix: list[tuple[str, bool]],
    ) -> None:
        def _process(items: list[tuple[str, bool]]) -> None:
            for text, is_cmd in items:
                if is_cmd:
                    assert not isinstance(
                        transient_shared_rdm.insert_command(text),
                        RocqDocManager.Err
                    )
                else:
                    transient_shared_rdm.insert_blanks(text)

        # Set up the document to contain a suffix and prefix of interleaved
        # blanks/commands
        _process(suffix)
        transient_shared_rdm.revert_before(False, 0)
        _process(prefix)

        with RDM_Tests.assert_doc_unchanged(transient_shared_rdm):
            with transient_shared_rdm.ctx(rollback=True):
                _process(rollback)


class Test_RDM_aborted_goal_ctx(RDM_Tests):
    @pytest.mark.parametrize('rollback', [True, False])
    def test_side_effects(
            self,
            transient_rdm: RocqDocManager,
            rollback: bool,
    ) -> None:
        goal = "True /\\ 1 = 1"
        tac = "intuition auto."
        cmds = [
            f"Goal {goal}.",
            tac,
            "Abort.",
        ]
        with (
                RDM_Tests.assert_doc_unchanged(transient_rdm)
                if rollback else
                RDM_Tests.assert_commands_inserted(transient_rdm, cmds=cmds)
        ):
            with transient_rdm.aborted_goal_ctx(goal=goal, rollback=rollback):
                idtac_reply = transient_rdm.run_command("idtac.")
                assert isinstance(idtac_reply, RocqDocManager.CommandData)
                assert idtac_reply.open_subgoals is not None
                # TODO: use structured proof state to make this more precise
                assert goal in idtac_reply.open_subgoals
                tac_reply = transient_rdm.insert_command(tac)
                assert isinstance(tac_reply, RocqDocManager.CommandData)
                # TODO: use structured proof state to make this more precise
                assert tac_reply.open_subgoals == "No more goals."


class Test_RDM_Section(RDM_Tests):
    def test_Context(self, transient_rdm: RocqDocManager) -> None:
        with RDM_Tests.assert_doc_unchanged(transient_rdm):
            context = [
                ("n", "nat"),
                ("b", "bool"),
                ("Hnb", "if b then n = 1 else n = 0")
            ]
            with transient_rdm.Section(
                    "test",
                    context=[f"({ident} : {ty})" for ident, ty in context],
                    rollback=True
            ):
                for ident, ty in context:
                    RDM_Tests.assert_check_ok(
                        transient_rdm,
                        term=ident,
                        lhs=ident,
                        rhs=ty,
                    )

# import pytest
from hypothesis import given, settings
from hypothesis import strategies as st
from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as api

from .util import RDM_Tests


class Test_RDM_macros(RDM_Tests):
    def test_current_goal_outside_proof(
        self,
        transient_rc: RocqCursor,
    ) -> None:
        outside_goal_reply = transient_rc.current_goal()
        assert outside_goal_reply is None
        with transient_rc.aborted_goal_ctx(goal="True", rollback=False):
            pass
        # NOTE: ignoring offset
        expected_prefix = [
            ("command", "Goal True."),
            ("blanks", "\n"),
            ("command", "Abort."),
            ("blanks", "\n"),
        ]
        prefix = transient_rc.doc_prefix()
        assert len(prefix) == len(expected_prefix)
        for i, (kind, text) in enumerate(expected_prefix):
            assert prefix[i].kind == kind, f"kind @ {i}"
            assert prefix[i].text == text, f"text @ {i}"
        outside_goal_reply = transient_rc.current_goal()
        assert outside_goal_reply is None

    def test_current_goal_True(
        self,
        transient_rc: RocqCursor,
    ) -> None:
        with transient_rc.aborted_goal_ctx(goal="True"):
            True_goal_reply = transient_rc.current_goal()
            assert not isinstance(True_goal_reply, api.Err)
            assert True_goal_reply is not None
            assert True_goal_reply.focused_goals == [
                "\n============================\nTrue"
            ]
            assert not isinstance(transient_rc.run_command("auto."), api.Err)
            closed_goal_reply = transient_rc.current_goal()
            assert not isinstance(closed_goal_reply, api.Err)
            assert closed_goal_reply is not None
            assert closed_goal_reply.focused_goals == []
            assert closed_goal_reply.unfocused_goals == []
            assert closed_goal_reply.given_up_goals == 0
            assert closed_goal_reply.shelved_goals == 0

    def test_current_goal_default_goal_selector_bang(
        self,
        transient_rc: RocqCursor,
    ) -> None:
        assert not isinstance(
            transient_rc.run_command('Set Default Goal Selector "!".'), api.Err
        )
        self.test_current_goal_True(transient_rc)

    def test_current_goal_done_up_to_one_shelved(
        self,
        transient_rc: RocqCursor,
    ) -> None:
        with transient_rc.aborted_goal_ctx(goal="exists _ : nat, True"):
            useless_existential_True_goal_reply = transient_rc.current_goal()
            assert not isinstance(useless_existential_True_goal_reply, api.Err)
            assert useless_existential_True_goal_reply is not None
            assert useless_existential_True_goal_reply.focused_goals == [
                "\n============================\nexists _ : nat, True"
            ]

            assert not isinstance(
                transient_rc.run_command("eexists; [shelve |]."),
                api.Err,
            )
            shelved_existential_True_goal_reply = transient_rc.current_goal()
            assert not isinstance(shelved_existential_True_goal_reply, api.Err)
            assert shelved_existential_True_goal_reply is not None
            assert shelved_existential_True_goal_reply.focused_goals == [
                "\n============================\nTrue"
            ]
            assert shelved_existential_True_goal_reply.shelved_goals == 1

            assert not isinstance(transient_rc.run_command("auto."), api.Err)

            assert transient_rc.run_command("idtac.") == api.Err(
                message="No such goal.", data=None
            )

            current_goal_reply = transient_rc.current_goal()
            assert not isinstance(current_goal_reply, api.Err)
            assert current_goal_reply is not None, (
                "When shelved goals remain, the current goal must not be None"
            )
            assert current_goal_reply.focused_goals == []
            assert current_goal_reply.shelved_goals == 1

    @given(
        n=st.integers(min_value=0, max_value=100),
        m=st.integers(min_value=0, max_value=100),
    )
    @settings(deadline=None)
    def test_Compute_addition(
        self,
        transient_shared_rc: RocqCursor,
        n: int,
        m: int,
    ) -> None:
        with RDM_Tests.assert_doc_unchanged(transient_shared_rc):
            with transient_shared_rc.ctx():
                compute_reply = transient_shared_rc.Compute(
                    f"{n}+{m}",
                )
                assert not isinstance(compute_reply, api.Err)
                assert compute_reply == (str(n + m), "nat")

    def test_fresh_ident_repeated(
        self,
        transient_rc: RocqCursor,
    ) -> None:
        with RDM_Tests.assert_doc_unchanged(transient_rc):
            with transient_rc.ctx():
                nm: str = "x"
                val: int | str = 0
                for _ in range(20):
                    defn = f"Definition {nm} := {val}."
                    assert not isinstance(
                        transient_rc.insert_command(defn),
                        api.Err,
                    ), f"Bad Definition: {defn}"
                    fresh_ident_reply = transient_rc.fresh_ident(nm)
                    assert not isinstance(fresh_ident_reply, api.Err)
                    val = nm
                    nm = fresh_ident_reply

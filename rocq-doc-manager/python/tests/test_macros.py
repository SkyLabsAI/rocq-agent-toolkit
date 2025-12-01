# import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from rocq_doc_manager import RocqDocManager

from .util import RDM_Tests


class Test_RDM_macros(RDM_Tests):
    def test_current_goal_outside_proof(
            self,
            transient_rdm: RocqDocManager,
    ) -> None:
        outside_goal_reply = transient_rdm.current_goal()
        assert outside_goal_reply == RocqDocManager.Err(
            message="Syntax error: illegal begin of vernac.",
            data=None,
        )
        with transient_rdm.aborted_goal_ctx(goal="True", rollback=False):
            pass
        # NOTE: ignoring offset
        expected_prefix = [
            ("command", "Goal True."),
            ("blanks", "\n"),
            ("command", "Abort."),
            ("blanks", "\n"),
        ]
        prefix = transient_rdm.doc_prefix()
        assert len(prefix) == len(expected_prefix)
        for i, (kind, text) in enumerate(expected_prefix):
            assert prefix[i].kind == kind
            assert prefix[i].text == text
        outside_goal_reply = transient_rdm.current_goal()
        assert outside_goal_reply == RocqDocManager.Err(
            message="Syntax error: illegal begin of vernac.",
            data=None,
        )

    def test_current_goal_True(
            self,
            transient_rdm: RocqDocManager,
    ) -> None:
        with transient_rdm.aborted_goal_ctx(goal="True"):
            True_goal_reply = transient_rdm.current_goal()
            assert not isinstance(True_goal_reply, RocqDocManager.Err)
            assert (
                True_goal_reply ==
                "1 goal\n  \n  ============================\n  True"
            )
            assert not isinstance(
                transient_rdm.run_command("auto."),
                RocqDocManager.Err
            )
            closed_goal_reply = transient_rdm.current_goal()
            assert not isinstance(closed_goal_reply, RocqDocManager.Err)
            assert closed_goal_reply is None

    def test_current_goal_default_goal_selector_bang(
            self,
            transient_rdm: RocqDocManager,
    ) -> None:
        assert not isinstance(
            transient_rdm.run_command("Set Default Goal Selector \"!\"."),
            RocqDocManager.Err
        )
        self.test_current_goal_True(transient_rdm)

    def test_current_goal_done_up_to_one_shelved(
            self,
            transient_rdm: RocqDocManager,
    ) -> None:
        with transient_rdm.aborted_goal_ctx(goal="exists _ : nat, True"):
            useless_existential_True_goal_reply = transient_rdm.current_goal()
            assert not isinstance(
                useless_existential_True_goal_reply,
                RocqDocManager.Err
            )
            assert (
                useless_existential_True_goal_reply ==
                "1 goal\n  \n  ============================\n  exists _ : nat, True"
            )

            assert not isinstance(
                transient_rdm.run_command("eexists; [shelve |]."),
                RocqDocManager.Err,
            )
            shelved_existential_True_goal_reply = transient_rdm.current_goal()
            assert not isinstance(
                shelved_existential_True_goal_reply,
                RocqDocManager.Err
            )
            assert (
                shelved_existential_True_goal_reply ==
                "1 focused goal (shelved: 1)\n  \n  ============================\n  True"
            )

            assert not isinstance(
                transient_rdm.run_command("auto."),
                RocqDocManager.Err
            )

            current_goal_reply = transient_rdm.current_goal()
            assert not isinstance(current_goal_reply, RocqDocManager.Err)
            assert current_goal_reply is not None, \
                "When shelved goals remain, the current goal must not be None"
            assert current_goal_reply == "\n1 goal\n\ngoal 1 is:\n nat"
            assert False, "Need to communicate that the goal is actually shelved."

    @given(
        n=st.integers(min_value=0, max_value=100),
        m=st.integers(min_value=0, max_value=100),
    )
    @settings(deadline=None)
    def test_Compute_addition(
            self,
            transient_shared_rdm: RocqDocManager,
            n: int,
            m: int,
    ) -> None:
        with RDM_Tests.assert_doc_unchanged(transient_shared_rdm):
            with transient_shared_rdm.ctx():
                compute_reply = transient_shared_rdm.Compute(
                    f"{n}+{m}",
                )
                assert not isinstance(compute_reply, RocqDocManager.Err)
                assert compute_reply == (str(n+m), "nat")

    def test_fresh_ident_repeated(
            self,
            transient_rdm: RocqDocManager,
    ) -> None:
        with RDM_Tests.assert_doc_unchanged(transient_rdm):
            with transient_rdm.ctx():
                nm: str = "x"
                val: int | str = 0
                for _ in range(20):
                    defn = f"Definition {nm} := {val}."
                    assert not isinstance(
                        transient_rdm.insert_command(defn),
                        RocqDocManager.Err,
                    ), f"Bad Definition: {defn}"
                    fresh_ident_reply = transient_rdm.fresh_ident(nm)
                    assert not isinstance(
                        fresh_ident_reply,
                        RocqDocManager.Err
                    )
                    val = nm
                    nm = fresh_ident_reply

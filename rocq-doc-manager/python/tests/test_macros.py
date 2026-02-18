# import pytest
from hypothesis import given, settings
from hypothesis import strategies as st
from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api

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
            ("command", "Proof."),
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

    def test_current_goal_False(
        self,
        transient_rc: RocqCursor,
    ) -> None:
        with transient_rc.aborted_goal_ctx('False', close = 'Abort'):
            x = transient_rc.insert_command("solve [trivial].")
            assert isinstance(x, rdm_api.Err) and x.message == 'No applicable tactic.', x
            # if isinstance(x, RocqCursor.Err):
                # raise AssertionError(x)



    def test_find_and_update(
        self,
        loadable_rc: RocqCursor,
    ) -> None:
        # def
        with loadable_rc.sess():
            assert not isinstance(loadable_rc.load_file(), rdm_api.Err)

            init_suff = loadable_rc.doc_suffix()
            assert loadable_rc.goto_first_match(
                lambda cmd, kind: cmd.startswith('intro'),
            )
            if loadable_rc.doc_suffix()[0].text == "intro x.":
                x = loadable_rc.insert_command("intro y.")
            else:
                assert loadable_rc.doc_suffix()[0].text == "intro y."
                x = loadable_rc.insert_command("intro x.")
            assert x
            assert x.proof_state
            assert (not x.proof_state.focused_goals ==
                    [ '\n'.join(["",
                                 "y : nat",
                                 "============================"
                                 "y = y'"]) ])

            loadable_rc.clear_suffix(1)
            blank = loadable_rc.doc_suffix()[0]
            if blank.kind == 'blanks':
                loadable_rc.clear_suffix(1)

            loadable_rc.go_to(0)
            cmd = init_suff[12].text
            if cmd == "intro x.":
                cmd = "intro y."
            else:
                assert cmd == "intro y."
                cmd = "intro x."
            init_suff[12] = rdm_api.SuffixItem(text = cmd, kind = 'command')
            init_suff[13] = rdm_api.SuffixItem(text = '\n', kind = 'blanks')
            assert loadable_rc.doc_suffix() == init_suff

            # loadable_rc.commit(file = None, include_suffix = True)


        # with loadable_rc.aborted_goal_ctx('False', close = 'Qed'):
        # with loadable_rc.aborted_goal_ctx('False', close = 'Qed'):
            # x = transient_rc.insert_command("solve [trivial].")
            # assert not isinstance(x, RocqCursor.Err), x.message
            # if isinstance(x, RocqCursor.Err):
                # raise AssertionError(x)

    def test_current_goal_True(
        self,
        transient_rc: RocqCursor,
    ) -> None:
        with transient_rc.aborted_goal_ctx(goal="True"):
            True_goal_reply = transient_rc.current_goal()
            assert not isinstance(True_goal_reply, rdm_api.Err)
            assert True_goal_reply is not None
            assert True_goal_reply.focused_goals == [
                "\n============================\nTrue"
            ]
            assert not isinstance(transient_rc.run_command("auto."), rdm_api.Err)
            closed_goal_reply = transient_rc.current_goal()
            assert not isinstance(closed_goal_reply, rdm_api.Err)
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
            transient_rc.run_command('Set Default Goal Selector "!".'), rdm_api.Err
        )
        self.test_current_goal_True(transient_rc)

    def test_current_goal_done_up_to_one_shelved(
        self,
        transient_rc: RocqCursor,
    ) -> None:
        with transient_rc.aborted_goal_ctx(goal="exists _ : nat, True"):
            useless_existential_True_goal_reply = transient_rc.current_goal()
            assert not isinstance(useless_existential_True_goal_reply, rdm_api.Err)
            assert useless_existential_True_goal_reply is not None
            assert useless_existential_True_goal_reply.focused_goals == [
                "\n============================\nexists _ : nat, True"
            ]

            assert not isinstance(
                transient_rc.run_command("eexists; [shelve |]."),
                rdm_api.Err,
            )
            shelved_existential_True_goal_reply = transient_rc.current_goal()
            assert not isinstance(shelved_existential_True_goal_reply, rdm_api.Err)
            assert shelved_existential_True_goal_reply is not None
            assert shelved_existential_True_goal_reply.focused_goals == [
                "\n============================\nTrue"
            ]
            assert shelved_existential_True_goal_reply.shelved_goals == 1

            assert not isinstance(transient_rc.run_command("auto."), rdm_api.Err)

            assert transient_rc.run_command("idtac.") == rdm_api.Err(
                message="No such goal.", data=None
            )

            current_goal_reply = transient_rc.current_goal()
            assert not isinstance(current_goal_reply, rdm_api.Err)
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
                assert not isinstance(compute_reply, rdm_api.Err)
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
                        rdm_api.Err,
                    ), f"Bad Definition: {defn}"
                    fresh_ident_reply = transient_rc.fresh_ident(nm)
                    assert not isinstance(fresh_ident_reply, rdm_api.Err)
                    val = nm
                    nm = fresh_ident_reply

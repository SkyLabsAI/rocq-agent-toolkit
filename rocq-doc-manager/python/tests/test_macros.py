import pytest
from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api

from .util import RDM_Tests


@pytest.mark.asyncio(loop_scope="class")
class Test_RDM_macros(RDM_Tests):
    async def test_current_goal_outside_proof(
        self,
        transient_rc: RocqCursor,
    ) -> None:
        outside_goal_reply = await transient_rc.current_goal()
        assert outside_goal_reply is None
        async with transient_rc.aborted_goal_ctx(goal="True", rollback=False):
            ...
        # NOTE: ignoring offset
        expected_prefix = [
            ("command", "Goal True."),
            ("blanks", "\n"),
            ("command", "Abort."),
            ("blanks", "\n"),
        ]
        prefix = await transient_rc.doc_prefix()
        assert len(prefix) == len(expected_prefix)
        for i, (kind, text) in enumerate(expected_prefix):
            assert prefix[i].kind == kind, f"kind @ {i}"
            assert prefix[i].text == text, f"text @ {i}"
        outside_goal_reply = await transient_rc.current_goal()
        assert outside_goal_reply is None

    async def test_current_goal_True(
        self,
        transient_rc: RocqCursor,
    ) -> None:
        async with transient_rc.aborted_goal_ctx(goal="True"):
            True_goal_reply = await transient_rc.current_goal()
            assert not isinstance(True_goal_reply, rdm_api.Err)
            assert True_goal_reply is not None
            assert True_goal_reply.focused_goals == [
                "\n============================\nTrue"
            ]
            assert not isinstance(await transient_rc.run_command("auto."), rdm_api.Err)
            closed_goal_reply = await transient_rc.current_goal()
            assert not isinstance(closed_goal_reply, rdm_api.Err)
            assert closed_goal_reply is not None
            assert closed_goal_reply.focused_goals == []
            assert closed_goal_reply.unfocused_goals == []
            assert closed_goal_reply.given_up_goals == 0
            assert closed_goal_reply.shelved_goals == 0

    async def test_current_goal_default_goal_selector_bang(
        self,
        transient_rc: RocqCursor,
    ) -> None:
        assert not isinstance(
            await transient_rc.run_command('Set Default Goal Selector "!".'),
            rdm_api.Err,
        )
        await self.test_current_goal_True(transient_rc)

    async def test_current_goal_done_up_to_one_shelved(
        self,
        transient_rc: RocqCursor,
    ) -> None:
        async with transient_rc.aborted_goal_ctx(goal="exists _ : nat, True"):
            useless_existential_True_goal_reply = await transient_rc.current_goal()
            assert not isinstance(useless_existential_True_goal_reply, rdm_api.Err)
            assert useless_existential_True_goal_reply is not None
            assert useless_existential_True_goal_reply.focused_goals == [
                "\n============================\nexists _ : nat, True"
            ]

            assert not isinstance(
                await transient_rc.run_command("eexists; [shelve |]."),
                rdm_api.Err,
            )
            shelved_existential_True_goal_reply = await transient_rc.current_goal()
            assert not isinstance(shelved_existential_True_goal_reply, rdm_api.Err)
            assert shelved_existential_True_goal_reply is not None
            assert shelved_existential_True_goal_reply.focused_goals == [
                "\n============================\nTrue"
            ]
            assert shelved_existential_True_goal_reply.shelved_goals == 1

            assert not isinstance(await transient_rc.run_command("auto."), rdm_api.Err)

            assert await transient_rc.run_command("idtac.") == rdm_api.Err(
                message="No such goal.", data=None
            )

            current_goal_reply = await transient_rc.current_goal()
            assert not isinstance(current_goal_reply, rdm_api.Err)
            assert current_goal_reply is not None, (
                "When shelved goals remain, the current goal must not be None"
            )
            assert current_goal_reply.focused_goals == []
            assert current_goal_reply.shelved_goals == 1

    @pytest.mark.parametrize("n,m", [(x, x) for x in range(10)])
    async def test_Compute_addition(
        self,
        transient_shared_rc: RocqCursor,
        n: int,
        m: int,
    ) -> None:
        async with RDM_Tests.assert_doc_unchanged(transient_shared_rc):
            async with transient_shared_rc.ctx():
                compute_reply = await transient_shared_rc.Compute(
                    f"{n}+{m}",
                )
                assert not isinstance(compute_reply, rdm_api.Err)
                assert compute_reply == (str(n + m), "nat")

    async def test_fresh_ident_repeated(
        self,
        transient_rc: RocqCursor,
    ) -> None:
        async with RDM_Tests.assert_doc_unchanged(transient_rc):
            async with transient_rc.ctx():
                nm: str = "x"
                val: int | str = 0
                for _ in range(20):
                    defn = f"Definition {nm} := {val}."
                    assert not isinstance(
                        await transient_rc.insert_command(defn),
                        rdm_api.Err,
                    ), f"Bad Definition: {defn}"
                    fresh_ident_reply = await transient_rc.fresh_ident(nm)
                    assert not isinstance(fresh_ident_reply, rdm_api.Err)
                    val = nm
                    nm = fresh_ident_reply

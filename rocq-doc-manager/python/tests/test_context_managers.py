import itertools

import pytest
from hypothesis import given, settings
from rocq_doc_manager import AsyncRocqDocManager, RocqCursor, rc_sess, rdm_sess
from rocq_doc_manager import rocq_doc_manager_api as rdm_api

from .util import LOADABLE_DOC, TRANSIENT_DOC, RDM_Tests


@pytest.mark.asyncio
# @pytest.mark.parametrize("rc", ["loadable_rc", "transient_rc"], indirect=True)
async def test_sess_no_load() -> None:
    async with rc_sess("./tests/test.v", load_file=False) as rc:
        await RDM_Tests.assert_check_ok(rc)


@pytest.mark.asyncio
async def test_sess_load() -> None:
    async with rc_sess("./tests/test.v", load_file=True) as rc:
        assert not isinstance(await rc.run_step(), rdm_api.Resp)
        await RDM_Tests.assert_check_ok(rc, term="N", lhs="N")


@pytest.mark.asyncio
async def test_sess_load_nonexistent() -> None:
    with pytest.raises(rdm_api.Error) as exc_info:
        async with rc_sess("my_fake.v"):
            ...
    assert exc_info.match("my_fake.v: No such file or directory")


@pytest.mark.parametrize(
    ("doc_path", "rollback"),
    list(
        itertools.product([(LOADABLE_DOC, True), (TRANSIENT_DOC, False)], [True, False])
    ),
)
@pytest.mark.asyncio
async def test_ctx_side_effects(
    doc_path: tuple[str, bool],
    rollback: bool,
) -> None:
    cmds = [f"Compute ({i}+{i})." for i in range(100)]
    path, load = doc_path
    async with rc_sess(path, load_file=load) as rc:
        ctx_expected = (
            RDM_Tests.assert_doc_unchanged(rc)
            if rollback
            else RDM_Tests.assert_commands_inserted(rc, cmds=cmds)
        )
        async with ctx_expected:
            async with rc.ctx(rollback=rollback):
                async with RDM_Tests.assert_commands_inserted(rc, cmds=cmds):
                    for cmd in cmds:
                        assert not isinstance(await rc.insert_command(cmd), rdm_api.Err)


@given(
    prefix=RDM_Tests.rocq_trivial_blank_cmd_sequence_strategy(),
    rollback=RDM_Tests.rocq_trivial_blank_cmd_sequence_strategy(),
    suffix=RDM_Tests.rocq_trivial_blank_cmd_sequence_strategy(),
)
@settings(deadline=None)
@pytest.mark.asyncio
async def test_property_rollback_ignores_blanks(
    prefix: list[tuple[str, bool]],
    rollback: list[tuple[str, bool]],
    suffix: list[tuple[str, bool]],
) -> None:
    async with rc_sess(TRANSIENT_DOC, load_file=False) as transient_shared_rc:

        async def _process(items: list[tuple[str, bool]]) -> None:
            for text, is_cmd in items:
                if is_cmd:
                    assert not isinstance(
                        await transient_shared_rc.insert_command(text), rdm_api.Err
                    )
                else:
                    await transient_shared_rc.insert_blanks(text)

        # Set up the document to contain a suffix and prefix of interleaved
        # blanks/commands
        await _process(suffix)
        await transient_shared_rc.revert_before(False, 0)
        await _process(prefix)

        async with RDM_Tests.assert_doc_unchanged(transient_shared_rc):
            async with transient_shared_rc.ctx(rollback=True):
                await _process(rollback)


@pytest.mark.parametrize("rollback", [True, False])
@pytest.mark.asyncio
async def test_aborted_goal_ctx_side_effects(
    rollback: bool,
) -> None:
    async with rc_sess(TRANSIENT_DOC, load_file=False) as rc:
        goal = "True /\\ 1 = 1"
        proof_goal = "\n============================\n" + goal
        tac = "intuition auto."
        cmds = [
            f"Goal {goal}.",
            tac,
            "Abort.",
        ]
        ctx_expected = (
            RDM_Tests.assert_doc_unchanged(rc)
            if rollback
            else RDM_Tests.assert_commands_inserted(rc, cmds=cmds)
        )
        async with ctx_expected:
            async with rc.aborted_goal_ctx(goal=goal, rollback=rollback):
                idtac_reply = await rc.run_command("idtac.")
                assert isinstance(idtac_reply, rdm_api.CommandData)
                assert idtac_reply.proof_state is not None
                assert idtac_reply.proof_state.focused_goals == [proof_goal]

                tac_reply = await rc.insert_command(tac)
                assert isinstance(tac_reply, rdm_api.CommandData)
                assert tac_reply.proof_state is not None
                assert tac_reply.proof_state.focused_goals == []
                assert tac_reply.proof_state.shelved_goals == 0
                assert tac_reply.proof_state.given_up_goals == 0
                assert tac_reply.proof_state.unfocused_goals == []


@pytest.mark.asyncio
async def test_Context() -> None:
    async with rc_sess(TRANSIENT_DOC, load_file=False) as rc:
        async with RDM_Tests.assert_doc_unchanged(rc):
            context = [
                ("n", "nat"),
                ("b", "bool"),
                ("Hnb", "if b then n = 1 else n = 0"),
            ]
            async with rc.Section(
                "test",
                context=[f"({ident} : {ty})" for ident, ty in context],
                rollback=True,
            ):
                for ident, ty in context:
                    await RDM_Tests.assert_check_ok(
                        rc,
                        term=ident,
                        lhs=ident,
                        rhs=ty,
                    )

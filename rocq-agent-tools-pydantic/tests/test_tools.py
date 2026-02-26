from __future__ import annotations

from hypothesis import given, settings as hypothesis_settings, strategies as st
import pytest
from unittest.mock import MagicMock

from pydantic_ai import RunContext

from rocq_doc_manager import RocqCursor, rc_sess
from rocq_doc_manager import rocq_doc_manager_api as rdm_api

from rocq_agent_tools_pydantic import tools


def _make_ctx[T](deps: T) -> RunContext[T]:
    """Create a mock RunContext with the given deps."""
    ctx = MagicMock(spec=RunContext)
    ctx.deps = deps
    return ctx


# Simulating a backtrack tool-call after many insert tool-calls
N_run_tactic_call = 5
@given(N_revert=st.integers(min_value=1, max_value=N_run_tactic_call))
@hypothesis_settings(deadline=None)
@pytest.mark.asyncio
async def test_run_tactic_backtrack_one_noop(N_revert: int) -> None:
    newline_separated_commands = [
        "Lemma maybe_hard (n m : nat) : n + m = m + m.",
        "Proof.",
        "Admitted.",
    ]
    admitted_idx = newline_separated_commands.index("Admitted.")

    async def assert_expected_proof_script(
        rc: RocqCursor,
        *,
        inserted_commands: list[str] | None = None,
    ) -> None:
        """"Assert: prefix+suffix matches expectation.

        Notes:
        - all commands separated by newlines
        - inserted_commands added just before prefix
        """
        expected_pf_script_str = "\n".join(
            newline_separated_commands[:admitted_idx] +
            (inserted_commands or [])+
            newline_separated_commands[admitted_idx:]
        ) + "\n"
        # NOTE: account for trailing newline that `setup_document_state`
        # implicitly inserts after `Admitted.`, by virtue of using `rc.insert_command`

        prefix_text = [prefix.text for prefix in await rc.doc_prefix()]
        suffix_text = [suffix.text for suffix in await rc.doc_suffix()]
        actual_pf_script_str = "".join(prefix_text + suffix_text)
        assert expected_pf_script_str == actual_pf_script_str


    async def setup_document_state(rc: RocqCursor) -> None:
        # 1) run the `Admitted.` proof
        for cmd in newline_separated_commands:
            result = await rc.insert_command(text=cmd, blanks=None)
            assert not isinstance(result, rdm_api.Err)
            await rc.insert_blanks(text="\n")
        await assert_expected_proof_script(rc)

        # 2) goto the beginning of the document
        result = await rc.go_to(0)
        assert not isinstance(result, rdm_api.Err)

        # 3) navigate to the point just before the `Admitted.` command,
        #    but /after/ its preceding blank
        assert await rc.goto_first_match(
            fn=lambda text, kind: kind == "command" and text == "Admitted."
        )

    async with rc_sess(
        "fake.v",
        rocq_args=[],
        dune=True,
        load_file=False,
    ) as rc:
        await setup_document_state(rc)
        # 1) document is setup properly:
        #    - after: the blank preceding the `"Admitted."` command
        #    - before: the `"Admitted."` command
        #    - [
        #          ...,
        #          blanks="\n",
        #          <HERE>,
        #          command="Admitted.",
        #      ]
        ctx = _make_ctx(tools.RocqProofStateDeps(rc))

        # 2) simulating: invoke run_tactic tool N_run_tactic_call times
        # 2a) `run_tactic` transitively invokes `rc.insert_command`
        # 2b) by default,`rc.insert_command` will pad with `blanks="\n"`
        command = "idtac."
        for _ in range(N_run_tactic_call):
            run_tactic_reply = await tools.run_tactic(ctx, command)
            assert run_tactic_reply.error is None
        await assert_expected_proof_script(
            rc,
            inserted_commands=[command] * N_run_tactic_call,
        )
        # 3) expected insertions are properly reflected in the document
        #    - after:
        #      + the newly inserted commands + padding blanks, cf. (2)
        #      + the blank preceding the `"Admitted."` command
        #    - before: the `"Admitted."` command
        #    - [
        #          ...,
        #          blanks="\n",
        #          [command=command, blanks="\n"] * N_run_tactic_call,
        #          <HERE>,
        #          command="Admitted.",
        #      ]

        # 4) simulating: backtracking before a random number of commands
        assert await tools.backtrack(ctx, N_revert)
        await assert_expected_proof_script(
            rc,
            inserted_commands=[command]*(N_run_tactic_call - N_revert),
        )
        # 5) document matches expectation
        #    - after:
        #      + the remaining newly inserted commands + padding blanks, cf. (2)
        #      + the blank preceding the `"Admitted."` command
        #    - before: the `"Admitted."` command
        #    - [
        #          ...,
        #          blanks="\n",
        #          [command=command, blanks="\n"] * (N_run_tactic_call - N_revert),
        #          <HERE>,
        #          command="Admitted.",
        #      ]

        # 6) simulating: backtracking the remainder
        assert await tools.backtrack(ctx, (N_run_tactic_call - N_revert))
        await assert_expected_proof_script(rc)
        # 7) document matches what it initially was:
        #    - after: the blank preceding the `"Admitted."` command
        #    - before: the `"Admitted."` command
        #    - [
        #          ...,
        #          blanks="\n",
        #          <HERE>,
        #          command="Admitted.",
        #      ]

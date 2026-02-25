import argparse
import asyncio
import difflib
import logging
import sys
from argparse import ArgumentParser
from pathlib import Path

from rocq_doc_manager import RocqCursor, rc_sess
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_dune_util import DuneError, rocq_args_for

from rocq_pipeline.agent import AgentBuilder
from rocq_pipeline.agent.proof.auto import AutoAgent
from rocq_pipeline.args_util import adapt_usage, split_args, valid_file

# TODOs:
# 1) proof formatter
# 2) properly handle `admit`s in addition to `Admitted`
# 3) properly handle nested proofs
# 4) parallel tasks:
#    - utilize `materialize` and/or `clone(materialize=True)`
#    - setup a `ThreadPoolExecutor` & use futures to manage interactions


# Notes:
# - this will ignore `admit`s
# - this will not properly handle whitespace between "Admitted" and period
def is_admitted(text: str, kind: str) -> bool:
    return kind == "command" and text == "Admitted."


async def run_proving_agent(
    rc: RocqCursor,
    agent_cls: AgentBuilder,
    output: Path,
    *,
    no_partial: bool = False,
) -> None:
    """Run the proving agent, delegating admitted proof tasks to agent_cls.

    Arguments:
        rc: the RocqCursor to use
        agent_cls: the AgentBuilder used to construct an Agent instance for each admitted proof task
        output: the Path where the result of the interaction should be committed
        no_partial (optional): whether or not the persist partial proof progress for each admitted proof task
    """
    if not filter(
        lambda suffix_item: is_admitted(suffix_item.text, suffix_item.kind),
        await rc.doc_suffix()
    ):
        print("No admitted proofs.")
        return

    print(
        f"Running the proving agent; partial proofs {'discarded' if no_partial else 'retained'}."
    )

    # Note: we could add `clone: bool = False` to `RocqCursorProtocolAsync.sess`
    # and transform `(await rc.clone()).sess()` into `await rc.sess(clone=True)`
    while await rc.goto_first_match(is_admitted):
        await run_delegated_prover_on_admitted_proof_task(
            agent_cls,
            rc,
            no_partial=no_partial,
        )

    await rc.commit(str(output), include_suffix=True)


async def run_delegated_prover_on_admitted_proof_task(
    agent_cls: AgentBuilder,
    rc: RocqCursor,
    *,
    no_partial: bool = False,
) -> None:
    """Use agent_cls to attempt the admitted proof task captured by the state of main_rc.

    Arguments:
        agent_cls: the AgentBuilder used to construct an Agent instance for the admitted proof task
        rc: the (shared) RocqCursor to use for the admitted proof task
        no_partial (optional): whether or not the persist partial proof progress for the admitted proof task
    """
    await print_admitted_proof_task(rc)

    # maybe not necessary
    async with (await rc.clone(materialize=True)).sess() as local_rc:
        await local_rc.clear_suffix()
        existing_prefix = await local_rc.doc_prefix()
        task_result = await agent_cls().run(rc=local_rc)

        async def agent_invariant_violated(message: str) -> None:
            print(message)
            # Step over `Admitted`
            await rc.run_step()
            pass

        # Insert partial progress if the proof is completed, or upon client request
        if task_result.success or (not no_partial):
            extended_prefix = await local_rc.doc_prefix()
            expected_overlapping_prefix = extended_prefix[: len(existing_prefix)]

            if existing_prefix != expected_overlapping_prefix:
                before = "".join([x.text for x in existing_prefix])
                after = "".join([x.text for x in extended_prefix])
                diff = difflib.unified_diff(a=before.split("\n"), b=after.split("\n"))
                return await agent_invariant_violated(
                    "\n".join(
                        ["Agent.prove invariant violated; prefix modified:"]
                        + list(diff)
                    )
                )

            extension = extended_prefix[len(existing_prefix) :]

            for prefix_item in extension:
                # What happens if agents try inserting ghost commands? Either:
                # - skip them
                # - insert them as a comment
                if prefix_item.kind == "blanks":
                    await rc.insert_blanks(text=prefix_item.text)
                else:
                    insert_result = await rc.insert_command(
                        text=prefix_item.text, blanks=None
                    )

                    if isinstance(insert_result, rdm_api.Err):
                        ####################################
                        # TODO: comment block with remaining
                        ####################################

                        return await agent_invariant_violated(
                            f"Agent.prove invariant violated; replaying proof script failed: {insert_result}"
                        )

            # TODO:
            # 1) write a few small test cases for the helper

            # 1a) check if last non-blank command in prefix is a `Qed`
            #
            # Note: brittle because agents could insert "extra" commands after `Qed`
            command_extension = [
                cmd for cmd in extension[::-1] if cmd.kind == "command"
            ]
            if len(command_extension) != 0 and command_extension[0].text == "Qed.":
                # Clear `Admitted.` from suffix if this code -- or the agent -- succeeded w/Qed
                # TODO: maybe check that the first item in the suffix is actually `Admitted`?
                await rc.clear_suffix(count=1)
            else:
                # 1b) else, try inserting Qed
                try_qed_result = await rc.insert_command(
                    "Qed."
                )  # TODO: maybe use `blanks=None`
                if not isinstance(try_qed_result, rdm_api.Err):
                    # Clear `Admitted.` from suffix if this code -- or the agent -- succeeded w/Qed
                    # MAYBE: clear until the next `Admitted`
                    await rc.clear_suffix(count=1)
                else:
                    # Step over `Admitted`
                    await rc.run_step()
        else:  # Step over `Admitted`
            await rc.run_step()

        # Print task_result and persistence
        if task_result.success:
            print(f"Agent succeeded: {task_result.message}")
        elif no_partial:
            print(
                f"Agent made partial progress, but ultimately failed: {task_result.message}"
            )
        else:
            print(f"Agent failed: {task_result.message}")


async def print_admitted_proof_task(local_rc: RocqCursor) -> None:
    """Print the admitted proof task captured by the state of main_rc."""

    goal = await local_rc.current_goal()
    assert goal is not None
    print(f"\nFound admit at index {await local_rc.cursor_index()}.")
    for i, g in enumerate(goal.focused_goals):
        print(f"Goal {i}:{g.replace('\n', '\n  ')}")


def agent_main(agent_builder: AgentBuilder) -> int:
    parser = ArgumentParser(
        description="""Run a proof agent on the given Rocq source file.
        Extra configuration options can be passed to the agent after a '--'.
        Pass '-h' or '--help' after the '--' to get agent options.""",
        exit_on_error=False,
    )
    parser.add_argument(
        "rocq_file",
        metavar="ROCQ_FILE",
        type=valid_file(exists=True, allowed_suffixes=[".v"]),
        help="file in which to attempt proof completion",
    )
    parser.add_argument(
        "-o",
        "--output",
        metavar="OUTPUT",
        type=valid_file(check_creatable=True, allowed_suffixes=[".v"]),
        help="output file (default is the input file)",
    )
    parser.add_argument(
        "--no-partial",
        action="store_true",
        help="discard partial proofs",
    )
    adapt_usage(parser, "agent")

    prover_args, agent_args = split_args()
    try:
        args = parser.parse_args(prover_args)
    except argparse.ArgumentError:
        parser.print_help()
        print()
        agent_builder.add_args(["--help"])
        return 0
    rocq_file = args.rocq_file
    if args.output is None:
        output: Path = rocq_file.name
    else:
        output = args.output
        if output.anchor == rocq_file.anchor:
            output = output.resolve()
    agent_builder.add_args(agent_args)
    logging.basicConfig(level=logging.ERROR)
    try:
        rocq_args = rocq_args_for(rocq_file, cwd=rocq_file.parent, build=True)

        async def _run() -> None:
            async with rc_sess(
                str(rocq_file.name),
                rocq_args=rocq_args,
                chdir=str(rocq_file.parent),
                dune=True,
                load_file=True,
            ) as rc:
                await run_proving_agent(
                    rc,
                    agent_builder,
                    output,
                    no_partial=args.no_partial,
                )

        asyncio.run(_run())
        return 0
    except DuneError as e:
        sys.exit(f"Error: could not find Rocq arguments for {rocq_file}.\n{e.stderr}")
    except Exception as e:
        sys.exit(f"Error: failed with {e}.")


def auto_prover():
    return agent_main(AgentBuilder.of_agent(AutoAgent))

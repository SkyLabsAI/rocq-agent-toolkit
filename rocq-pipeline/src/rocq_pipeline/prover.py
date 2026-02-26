import argparse
import asyncio
import difflib
import logging
import sys
from argparse import ArgumentParser
from collections.abc import Sequence
from dataclasses import dataclass
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


@dataclass
class FileOffset:
    line: int  # first line is 0
    col: int
    offset: int


async def cursor_offset(rc: RocqCursor) -> FileOffset:
    """Compute the offset of a RocqCursor.

    TODO: This function should probably be replaced with something else"""
    prefix = await rc.doc_prefix()
    contents = "".join(x.text for x in prefix if x.kind != "ghost")
    if contents == "":
        return FileOffset(line=0, col=0, offset=0)
    offset = len(contents)
    lines = contents.splitlines()
    line = max(0, len(lines))
    if contents[-1] == "\n":
        col = 0
    else:
        col = len(lines[-1])
    return FileOffset(line=line, col=col, offset=offset)


async def run_proving_agent(
    rc: RocqCursor,
    agent_cls: AgentBuilder,
    output: Path,
    *,
    partial: bool = False,
) -> None:
    """Run the proving agent, delegating admitted proof tasks to agent_cls.

    Arguments:
        rc: the RocqCursor to use
        agent_cls: the AgentBuilder used to construct an Agent instance for each admitted proof task
        output: the Path where the result of the interaction should be committed
        partial (optional): whether or not the persist partial proof progress for each admitted proof task
    """
    suffix_items_admitted = [
        suffix_item
        for suffix_item in await rc.doc_suffix()
        if is_admitted(suffix_item.text, suffix_item.kind)
    ]

    if not suffix_items_admitted:
        print("No admitted proofs.")
        return

    admitted_cnt = len(suffix_items_admitted)
    plural = "" if admitted_cnt == 1 else "s"
    partial_proof_handling = "retained" if partial else "discarded"
    print(
        f"Running the proving agent on {admitted_cnt} admitted proof{plural}; partial proofs will be {partial_proof_handling}."
    )

    # Note: we could add `clone: bool = False` to `RocqCursorProtocolAsync.sess`
    # and transform `(await rc.clone()).sess()` into `await rc.sess(clone=True)`
    while await rc.goto_first_match(is_admitted):
        await run_delegated_prover_on_admitted_proof_task(
            agent_cls,
            rc,
            partial=partial,
        )

    remaining_suffix_items = await rc.doc_suffix()
    if remaining_suffix_items:
        remaining_suffix_items_admitted = [
            suffix_item
            for suffix_item in remaining_suffix_items
            if is_admitted(suffix_item.text, suffix_item.kind)
        ]
        processed_admitted_cnt = admitted_cnt - len(remaining_suffix_items_admitted)
        if processed_admitted_cnt != admitted_cnt:
            processed_plural = "" if processed_admitted_cnt == 1 else "s"
            run_step_response = await rc.run_step()
            if isinstance(run_step_response, rdm_api.Err):
                proximal_cause = "\n".join(
                    [
                        ":\n",
                        remaining_suffix_items[0].text,
                        "",
                        run_step_response.message,
                    ]
                )
            else:
                proximal_cause = "."

            print(
                f"\nCommand failure after processing {processed_admitted_cnt} admitted proof{processed_plural}{proximal_cause}"
            )

    await rc.commit(str(output), include_suffix=True)


async def run_delegated_prover_on_admitted_proof_task(
    agent_cls: AgentBuilder,
    rc: RocqCursor,
    *,
    partial: bool = False,
) -> None:
    """Use agent_cls to attempt the admitted proof task captured by the state of main_rc.

    Arguments:
        agent_cls: the AgentBuilder used to construct an Agent instance for the admitted proof task
        rc: the (shared) RocqCursor to use for the admitted proof task
        partial (optional): whether or not the persist partial proof progress for the admitted proof task
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

        # Insert partial progress if the proof is completed, or upon client request
        doc_modified = False
        if task_result.success or partial:
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
            if not await try_replay(rc, extension):
                return await agent_invariant_violated(
                    "Agent.prove invariant violated; replaying the proof script failed"
                )

            # 1a) check if last non-blank command in prefix is a `Qed`
            #
            # Note: brittle because agents could insert "extra" commands after `Qed`
            command_extension = [
                cmd for cmd in extension[::-1] if cmd.kind == "command"
            ]
            doc_modified = len(command_extension) != 0
            if len(command_extension) != 0 and command_extension[0].text == "Qed.":
                # Clear `Admitted.` from suffix if this code -- or the agent -- succeeded w/Qed
                await rc.clear_suffix(count=1)
            else:
                # 1b) else, try inserting Qed
                try_qed_result = await rc.insert_command(
                    "Qed.",
                    blanks=None,
                )
                if not isinstance(try_qed_result, rdm_api.Err):
                    # Clear `Admitted.` from suffix if this code -- or the agent -- succeeded w/Qed
                    await rc.clear_suffix(count=1)
                else:
                    # Step over `Admitted`
                    await rc.run_step()
        else:  # Step over `Admitted`
            await rc.run_step()

        # Print task_result and persistence
        if task_result.success:
            msg = "Agent succeeded"
        elif partial and doc_modified:
            msg = "Agent made partial progress"
        else:
            msg = "Agent failed"

        if task_result.message:
            print(f"{msg}:\n{task_result.message}")
        else:
            print(f"{msg}.")


async def try_replay(
    rc: RocqCursor,
    interaction: Sequence[rdm_api.PrefixItem],
    *,
    include_ghost: bool = True,
) -> bool:
    """Try to replay the interaction in rc.

    Arguments:
        rc: RocqCursor that will try to replay the interaction
        interaction: sequence of `rdm_api.PrefixItem`s
        include_ghost (optional): whether or not to include ghost interactions as comments
    Side Effect:
        rc: replay as much of the interaction as possible:
        - blanks: inserted as-is
        - commands:
          + ghost=False: inserted as-is, or as comments iff a previous insertion failed
          + ghost=True: inserted as comments; ignored iff include_ghost=False
    """
    for i, prefix_item in enumerate(interaction):
        if prefix_item.kind == "blanks":
            await rc.insert_blanks(text=prefix_item.text)
        elif prefix_item.kind == "ghost" and include_ghost:
            await rc.insert_blanks(text=f"(* {prefix_item.text} *)")
        elif prefix_item.kind == "command":
            insert_result = await rc.insert_command(text=prefix_item.text, blanks=None)

            if isinstance(insert_result, rdm_api.Err):
                await rc.insert_blanks(
                    text=(
                        "(*"
                        + prefix_item.text
                        + "".join(x.text for x in interaction[i + 1 :])
                        + "*)"
                    )
                )
                return False

    return True


async def print_admitted_proof_task(local_rc: RocqCursor) -> None:
    """Print the admitted proof task captured by the state of main_rc."""

    goal = await local_rc.current_goal()
    assert goal is not None
    position = await cursor_offset(local_rc)
    print(
        f"\nFound admit at line {position.line + 1}, column {position.col} (offset={position.offset})."
    )
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
        print("Gathering Rocq configuration...")
        rocq_args = rocq_args_for(rocq_file, cwd=rocq_file.parent, build=True)

        async def _run() -> None:
            print("Loading file...")
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
                    partial=not args.no_partial,
                )

        asyncio.run(_run())
        return 0
    except DuneError as e:
        sys.exit(f"Error: could not find Rocq arguments for {rocq_file}.\n{e.stderr}")
    except Exception as e:
        sys.exit(f"Error: failed with {e}.")


def auto_prover():
    return agent_main(AgentBuilder.of_agent(AutoAgent))

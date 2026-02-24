import argparse
import asyncio
import logging
import sys
from argparse import ArgumentParser
from pathlib import Path

from rocq_doc_manager import RocqCursor, rc_sess
from rocq_dune_util import DuneError, rocq_args_for

from rocq_pipeline.agent import AgentBuilder
from rocq_pipeline.agent.proof.auto import AutoAgent
from rocq_pipeline.args_util import adapt_usage, split_args, valid_file


# TODOs:
# 1) properly handle `admit`s in addition to `Admitted`
# 2) parallel tasks:
#    - utilize `materialize` and/or `clone(materialize=True)`
#    - setup a `ThreadPoolExecutor` & use futures to manage interactions


# Note: this will ignore `admit`s
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
    print(
        f"Running the proving agent; partial proofs {'discarded' if no_partial else 'retained'}."
    )

    # Note: we could add `clone: bool = False` to `RocqCursorProtocolAsync.sess`
    # and transform `(await rc.clone()).sess()` into `await rc.sess(clone=True)`
    with (await rc.clone()).sess() as main_rc:
        while await main_rc.goto_first_match(is_admitted):
            await run_delegated_prover_on_admitted_proof_task(
                agent_cls,
                main_rc,
                no_partial=no_partial,
            )

    await main_rc.commit(str(output), include_suffix=True)


async def run_delegated_prover_on_admitted_proof_task(
    agent_cls: AgentBuilder,
    main_rc: RocqCursor,
    *,
    no_partial: bool = False,
) -> None:
    """Use agent_cls to attempt the admitted proof task captured by the state of main_rc.

    Arguments:
        agent_cls: the AgentBuilder used to construct an Agent instance for the admitted proof task
        main_rc: the (shared) RocqCursor to use for the admitted proof task
        no_partial (optional): whether or not the persist partial proof progress for the admitted proof task
    """
    await print_admitted_proof_task(main_rc)

    with (await main_rc.clone()).sess() as local_rc:
        task_result = await agent_cls().run(rc=local_rc)

        should_persist = task_result.success or

        # NOTE: the pattern of switching to the other cursor is not great
        # here, we should really copy the contents into the document.
        # Doing this will enable some parallelization if we want.
        if task_result.success:
            print(f"Agent succeeded: {task_result.message}")
            await local_rc.clear_suffix(count=1)
            await local_rc.insert_command("Qed.", blanks=None)
            old_rc = main_rc
            main_rc = local_rc
            await old_rc.dispose()
        else:
            print(f"Agent failed: {task_result.message}")
            await local_rc.dispose()
            await main_rc.run_step()


async def print_admitted_proof_task(main_rc: RocqCursor) -> None:
    """Print the admitted proof task captured by the state of main_rc."""

    goal = await main_rc.current_goal()
    assert goal is not None
    print(f"\nFound admit at index {await main_rc.cursor_index()}.")
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
        output = rocq_file.name
    else:
        output: Path = args.output
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

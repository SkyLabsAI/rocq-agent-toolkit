import asyncio
import logging
import sys
from argparse import ArgumentParser
from pathlib import Path

from rocq_doc_manager import RocqCursor, rc_sess
from rocq_dune_util import DuneError, rocq_args_for

from rocq_pipeline.agent import AgentBuilder
from rocq_pipeline.agent.proof.auto import AutoAgent
from rocq_pipeline.args_util import valid_file


def is_admitted(text: str, kind: str) -> bool:
    return kind == "command" and text == "Admitted."


async def run_proving_agent(
    rc: RocqCursor, agent_cls: AgentBuilder, output: Path
) -> None:
    main_rc = await rc.clone()
    print("Running the proving agent.")
    while await main_rc.goto_first_match(is_admitted):
        print()
        goal = await main_rc.current_goal()
        assert goal is not None
        print(f"Found admit at index {await main_rc.cursor_index()}.")
        for i, g in enumerate(goal.focused_goals):
            print(f"Goal {i}:{g.replace('\n', '\n  ')}")
        agent = agent_cls()  # Build the actual agent to run
        local_rc = await main_rc.clone()  # should materialize this
        task_result = await agent.run(rc=local_rc)

        # NOTE: the pattern of switching to the other cursor is not great
        # here, we should really copy the contents into the document.
        # Doing this will enable some parallelization if we want.
        if task_result.success:
            print("Agent succeeded.")
            await local_rc.clear_suffix(count=1)
            await local_rc.insert_command("Qed.", blanks=None)
            old_rc = main_rc
            main_rc = local_rc
            await old_rc.dispose()
        else:
            print("Agent failed.")
            await local_rc.dispose()
            await main_rc.run_step()
    await main_rc.commit(str(output), include_suffix=True)


# TODO: upstream
def split_args(argv: list[str] | None = None) -> tuple[list[str], list[str]]:
    args = sys.argv[1:] if argv is None else argv
    extra_args: list[str] = []
    try:
        idx = args.index("--")
        extra_args = args[idx + 1 :]
        args = args[:idx]
    except ValueError:
        pass
    return (args, extra_args)


def agent_main(agent_builder: AgentBuilder) -> bool:
    parser = ArgumentParser(
        description="Run a proof agent on the given Rocq source file."
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
    prover_args, agent_args = split_args()
    args = parser.parse_args(prover_args)
    rocq_file = args.rocq_file
    if args.output is None:
        output = rocq_file.name
    else:
        output = args.output
        if output.anchor == rocq_file.anchor:
            output = output.relative_to(rocq_file.parent, walk_up=True)
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
                await run_proving_agent(rc, agent_builder, output)

        asyncio.run(_run())
        return True
    except DuneError as e:
        sys.exit(f"Error: could not find Rocq arguments for {rocq_file}.\n{e.stderr}")
    except Exception as e:
        sys.exit(f"Error: failed with {e}.")


def auto_prover():
    return 0 if agent_main(AgentBuilder.of_agent(AutoAgent)) else 1

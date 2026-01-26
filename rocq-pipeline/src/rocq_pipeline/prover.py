import logging
import sys
from argparse import ArgumentParser
from pathlib import Path

from rocq_doc_manager import DuneUtil, RocqCursor, RocqDocManager

from rocq_pipeline.agent import ProofAgent


def is_admitted(text: str, kind: str) -> bool:
    return kind == "command" and text == "Admitted."


def run_proving_agent(
    rc: RocqCursor, agent_cls: type[ProofAgent], output: Path
) -> None:
    main_rc = rc.clone()
    print("Running the proving agent.")
    while main_rc.advance_to_first_match(is_admitted):
        print()
        goal = main_rc.current_goal()
        assert goal is not None
        print(f"Found admitted at index {main_rc.cursor_index()}.")
        for i, g in enumerate(goal.focused_goals):
            print(f"Goal {i}:{g.replace('\n', '\n  ')}")
        agent = agent_cls()
        local_rc = main_rc.clone()
        task_result = agent.run(rc=local_rc)
        if task_result.success:
            print("Agent succeeded.")
            local_rc.clear_suffix(count=1)
            local_rc.insert_command("Qed.", blanks=None)
            old_rc = main_rc
            main_rc = local_rc
            old_rc.dispose()
        else:
            print("Agent failed.")
            local_rc.dispose()
            main_rc.run_step()
    main_rc.commit(str(output), include_suffix=True)


def check_rocq_file(file: str) -> Path:
    path = Path(file)
    if not path.exists():
        sys.exit(f"Error: file {path} does not exist.")
    if path.suffix != ".v":
        sys.exit(f'Error: file {path} does not have ".v" extension.')
    return path


def main_prover(agent_cls: type[ProofAgent]):
    parser = ArgumentParser(
        description="Run a proof agent on the given Rocq source file."
    )
    parser.add_argument(
        "rocq_file",
        metavar="ROCQ_FILE",
        type=check_rocq_file,
        help="file in which to attempt proof completion",
    )
    parser.add_argument(
        "-o",
        "--output",
        metavar="OUTPUT",
        type=Path,
        help="output file (default is the input file)",
    )
    args = parser.parse_args()
    rocq_file = args.rocq_file
    if args.output is None:
        output = rocq_file.name
    else:
        output = args.output
        if output.anchor == rocq_file.anchor:
            output = output.relative_to(rocq_file.parent, walk_up=True)
    logging.basicConfig(level=logging.ERROR)
    try:
        rocq_args = DuneUtil.rocq_args_for(
            rocq_file.name, cwd=rocq_file.parent, build=True
        )
        with RocqDocManager(
            rocq_args, str(rocq_file.name), dune=True, chdir=str(rocq_file.parent)
        ).sess(load_file=True) as rdm:
            run_proving_agent(rdm.cursor(), agent_cls, output)
    except DuneUtil.NotFound:
        sys.exit(f"Error: could not find Rocq arguments for {rocq_file}.")
    except Exception as e:
        sys.exit(f"Error: failed with {e}.")

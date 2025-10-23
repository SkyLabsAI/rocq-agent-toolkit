"""Task runner for executing automated theorem proving tasks.

This module provides functionality to run agents on Coq proof tasks,
including argument parsing, task loading, and result reporting.
"""

import argparse
import json
from pathlib import Path
import sys
from typing import Type, Optional

from rocq_doc_manager import RocqDocManager  # type: ignore
from rocq_pipeline.agent import GiveUp, Finished, Agent
from rocq_pipeline import locator
from rocq_pipeline.auto_agent import AutoAgent
import rocq_pipeline.tasks as Tasks


def main(agent_type: Type[Agent], args: Optional[list[str]] = None) -> bool:
    """Run the given agent on the specified tasks.

    This function parses command-line arguments, loads tasks from files or JSON,
    and runs the specified agent on each task.

    Args:
        agent_type: The type of agent to instantiate and run.
        args: Optional list of command-line arguments. If None, uses sys.argv[1:].

    Returns:
        True if all tasks were processed successfully, False otherwise.
    """
    if args is None:
        args = sys.argv[1:]

    # Set up the argument parser
    parser = argparse.ArgumentParser(
        description="Parses a file name, an optional trace flag, and collects all arguments following a '--' separator.",
        epilog="Example usage:\n  python proof_driver.py [--trace] proof.v [-- Rocq parameters]",
    )
    # Add the single required positional argument
    parser.add_argument(
        "--task-json", type=json.loads, help="The task descriptor, as JSON."
    )
    parser.add_argument(
        "--task-file", type=Path, help="The task descriptor in a file, JSON or YAML"
    )
    # Add the optional --trace flag
    parser.add_argument("--trace", action="store_true", help="Enable tracing.")

    # Allow the agent to set up additional arguments
    # TODO: if this function is not defined, then it shouldn't
    # do anything
    if hasattr(agent_type, "arg_parser"):
        agent_type.arg_parser(parser)

    arguments = parser.parse_args(args)

    wdir = Path(".")
    tasks: list[dict] = []
    if not arguments.task_json is None:
        assert arguments.task_file is None
        tasks = [arguments.task_json]
    elif not arguments.task_file is None:
        (wdir, tasks) = Tasks.load_tasks(arguments.task_file)
    else:
        print("unspecified task")
        return False

    for task in tasks:
        rdm = RocqDocManager([], str(wdir / task["file"]), dune=True)
        rdm.load_file()
        if not locator.parse_locator(task["locator"])(rdm):
            print("locator returned false")
            continue

        if hasattr(agent_type, "build"):
            # TODO: should we remove any attributes from the task
            agent = agent_type.build(
                prompt=task["prompt"] if "prompt" in task else None, args=args
            )
        else:
            agent = agent_type()

        result = agent.run(rdm)
        if isinstance(result, GiveUp):
            print(f"agent gave up with message: {result.message}")
        elif isinstance(result, Finished):
            print(f"task completed: {result.message}")

    return True


def auto_main() -> bool:
    """Run the AutoAgent on tasks specified via command line.

    This is a convenience function that runs the AutoAgent using
    the main task runner function.

    Returns:
        True if all tasks were processed successfully, False otherwise.
    """
    return main(AutoAgent)

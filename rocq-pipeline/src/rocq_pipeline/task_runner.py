import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import json
import sys
from pathlib import Path
import threading
from typing import Any, Optional, Type
import uuid

from rocq_doc_manager import RocqDocManager

import rocq_pipeline.tasks as Tasks
from rocq_pipeline import locator
from rocq_pipeline.agent import Agent, Finished, GiveUp, TaskResult
from rocq_pipeline.auto_agent import AutoAgent
from rocq_pipeline.locator import parse_locator
from rocq_pipeline.schema import task_output


def mk_argparser(agent_type: Type[Agent]) -> argparse.ArgumentParser:
    # Set up the argument parser
    parser = argparse.ArgumentParser(
        description="Parses a file name, an optional trace flag, and collects all arguments following a '--' separator.",
        epilog="Example usage:\n  python proof_driver.py [--trace] proof.v [-- Rocq parameters]",
    )
    # Add the single required positional argument
    parser.add_argument("--task-json", type=json.loads, help="The task descriptor, as JSON.")
    parser.add_argument(
        "--task-file", type=Path, help="The task descriptor in a file, JSON or YAML"
    )
    # Add the optional --trace flag
    parser.add_argument("--trace", action="store_true", help="Enable tracing.")
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("."),
        help="The directory to output task results, as JSONL."
    )
    parser.add_argument(
        "-j", "--jobs",
        type=lambda N: max(1, int(N)),
        default=1,
        help="The number of parallel workers."
    )

    # Allow the agent to set up additional arguments
    # TODO: if this function is not defined, then it shouldn't
    # do anything
    if hasattr(agent_type, "arg_parser"):
        agent_type.arg_parser(parser)

    return parser


def main(agent_type: Type[Agent], args: Optional[list[str]] = None) -> bool:
    if args is None:
        args = sys.argv[1:]

    arguments = mk_argparser(agent_type).parse_args(args)

    wdir = Path(".")
    tasks: list[dict] = []
    tasks_name: str = "tasks"
    if arguments.task_json is not None:
        # TODO: if we had a schema we could automatically validate that the
        # task JSON has the expected shape.
        assert arguments.task_file is None
        tasks = Tasks.mk_validated_tasklist(arguments.task_json)
    elif arguments.task_file is not None:
        (wdir, tasks) = Tasks.load_tasks(arguments.task_file)
        tasks_name = arguments.task_file.stem
    else:
        print("unspecified task")
        return False

    now_str = datetime.now().strftime("%Y%m%d_%H%M")
    tasks_result_file: Path = (
        arguments.output_dir / f"{tasks_name}_results_{now_str}.jsonl"
    )
    run_id: str = str(uuid.uuid4())

    def run_task(task: dict[str, Any]) -> task_output.TaskOutput | None:
        # TODO: find a better ID for tasks
        task_id: str = f"{task['file']}#{task['locator']}"
        # TODO: integrate with opentelemetry, properly instrument the agent
        # framework and derived agents
        trace_id: str | None = None
        timestamp_iso_8601 = datetime.now(timezone.utc).isoformat()

        task_result: TaskResult | None = None
        try:
            with RocqDocManager(
                    [],
                    str(wdir / task["file"]),
                    dune=True,
            ) as rdm:
                assert isinstance(rdm.load_file(), RocqDocManager.Resp)

                if not locator.parse_locator(task["locator"])(rdm):
                    print(f"{task_id}: locator returned false")
                    return None

                if hasattr(agent_type, "build"):
                    # TODO: should we remove any attributes from the task
                    agent = agent_type.build(
                        prompt=task["prompt"] if "prompt" in task else None,
                        args=args
                    )
                else:
                    agent = agent_type()

                task_result = agent.run(rdm)
        except Exception as e:
            task_result = GiveUp.from_exception(e)
        assert task_result is not None

        task_failure_reason: task_output.FailureReason | None = None
        if isinstance(task_result, GiveUp):
            task_status = task_output.TaskStatus(task_output.Failure())
            task_failure_reason = task_output.FailureReason(
                task_output.Other(task_result.message)
            )
            print(f"agent gave up with message: {task_result.message}")
        elif isinstance(task_result, Finished):
            task_status = task_output.TaskStatus(task_output.Success())
            print(f"task completed: {task_result.message}")

        return task_output.TaskOutput(
            run_id=run_id,
            task_kind=parse_locator(task["locator"]).task_kind(),
            task_id=task_id,
            trace_id=trace_id,
            timestamp_utc=timestamp_iso_8601,
            agent_name=agent.name(),
            status=task_status,
            results=task_result.final_doc_interaction,
            failure_reason=task_failure_reason,
            metrics=task_result.metrics,
        )

    with ThreadPoolExecutor(arguments.jobs) as tpe:
        # NOTE: iterator blocks if the next result has not been yielded
        for result in tpe.map(run_task, tasks):
            if result is not None:
                with open(tasks_result_file, "a", encoding="utf8") as f:
                    json.dump(result.to_json(), f)
                    f.write("\n")

    return True


def auto_main() -> bool:
    return main(AutoAgent)

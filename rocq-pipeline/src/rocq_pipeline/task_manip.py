import argparse
import random
from pathlib import Path
from typing import Any

import rocq_pipeline.tasks as Tasks
from rocq_pipeline.tasks import Task


def mk_parser(parent: Any|None=None) -> Any:
    # Set up the argument parser
    if parent:
        parser = parent.add_parser("filter", help="Process tasks")
    else:
        parser = argparse.ArgumentParser(description="Process tasks.")

    parser.add_argument(
        "--output",
        type=Path,
        required=True,
        help="The file to write the result to (.json or .yaml)."
    )
    parser.add_argument(
        "--with-tag",
        type=str,
        nargs='*',
        help="Keeps tasks with the given tag"
    )
    parser.add_argument(
        "--without-tag",
        type=str,
        nargs='*',
        help="Keeps tasks that do not have the given tag"
    )
    parser.add_argument("--limit", type=lambda x: max(0, int(x)), help="The maximum number of results to return")
    parser.add_argument("--random", action='store_true', help="Used in conjunction with --max to select random tasks")

    parser.add_argument(
            'task_file',
            type=Path,
            help='The path to the task file'
        )

    return parser

def run(output: Path, wdir: Path, tasks: list[Task], with_tags: set[str] | None=None, without_tags:set[str] | None=None, limit:int|None = None, random_selection:bool=False) -> list[Task]:
    def keep(task: Task) -> bool:
        if 'tags' in task:
            keep = with_tags is None or all(tag in task['tags'] for tag in with_tags)
            remove = without_tags is not None and any(tag in task['tags'] for tag in without_tags)
            return keep and not remove
        return with_tags is None or len(with_tags) == 0
    result_tasks = [task for task in tasks if keep(task)]
    if limit is not None:
        limit = min(limit, len(result_tasks))
        if random_selection:
            result_tasks = random.sample(result_tasks, limit)
        else:
            result_tasks = result_tasks[:limit]
    # TODO: Should this adapt the file paths to be relative to the output directory
    Tasks.save_tasks(output, result_tasks)
    return result_tasks

def run_ns(arguments: argparse.Namespace, extra_args:list[str]|None=None) -> None:
    assert extra_args is None or len(extra_args) == 0
    (wdir, tasks) = Tasks.load_tasks(arguments.task_file)
    result = run(arguments.output, wdir, tasks, arguments.with_tag, arguments.without_tag, arguments.limit, arguments.random)
    print(f"Returned {len(result)} of {len(tasks)} tasks.")

def main() -> None:
    run_ns(mk_parser().parse_args())

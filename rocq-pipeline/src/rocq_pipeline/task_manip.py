import argparse
import random
from pathlib import Path
from typing import Any

from rocq_pipeline.tasks import Task, TaskFile


def mk_parser(parent: Any | None = None) -> Any:
    # Set up the argument parser
    if parent:
        parser = parent.add_parser("filter", help="Process tasks")
    else:
        parser = argparse.ArgumentParser(description="Process tasks.")

    parser.add_argument(
        "--output",
        type=Path,
        required=True,
        help="The file to write the result to (.json or .yaml).",
    )
    parser.add_argument(
        "--with-tag", type=str, nargs="*", help="Keeps tasks with the given tag"
    )
    parser.add_argument(
        "--without-tag",
        type=str,
        nargs="*",
        help="Keeps tasks that do not have the given tag",
    )
    parser.add_argument(
        "--only-tags",
        type=str,
        help="Keep tasks that only have a subset of these tags. (separated by ,)",
    )
    parser.add_argument(
        "--limit",
        type=lambda x: max(0, int(x)),
        help="The maximum number of results to return",
    )
    parser.add_argument(
        "--random",
        action="store_true",
        help="Used in conjunction with --limit to select random tasks",
    )

    parser.add_argument("task_file", type=Path, help="The path to the task file")

    return parser


def eval_options(
    tags: set[str],
    with_tags: list[str],
    without_tags: list[str],
    only_tags: str | None = None,
) -> bool:
    ts: set[str] = set(tags)
    if only_tags and not ts.issubset({x.strip() for x in only_tags.split(",")}):
        return False

    def check_tag(tag: str, default: bool = True) -> bool:
        tag = tag.strip()
        if tag == "":
            return default
        for ctag in tag.split("|"):
            if ctag.strip() in tags:
                return True
        return False

    keep = with_tags is None or all(check_tag(tag, default=True) for tag in with_tags)
    remove = without_tags is not None and any(
        check_tag(tag, default=False) for tag in without_tags
    )
    return keep and not remove


def run(
    output: Path,
    tasks: TaskFile,
    with_tags: set[str] | None = None,
    without_tags: set[str] | None = None,
    only_tags: str | None = None,
    limit: int | None = None,
    random_selection: bool = False,
) -> TaskFile:
    def norm(ts: set[str] | None) -> list[str]:
        if ts is None:
            return []
        else:
            return [tag for tag in ts if tag != ""]

    with_tags_l = norm(with_tags)
    without_tags_l = norm(without_tags)

    def keep(task: Task) -> bool:
        return eval_options(task.get_tags(), with_tags_l, without_tags_l, only_tags)

    result_tasks = [task for task in tasks.tasks if keep(task)]
    if limit is not None:
        limit = min(limit, len(result_tasks))
        if random_selection:
            result_tasks = random.sample(result_tasks, limit)
        else:
            result_tasks = result_tasks[:limit]

    result = TaskFile(project=tasks.project, tasks=result_tasks)
    result.to_file(output)
    return result


def run_ns(arguments: argparse.Namespace, extra_args: list[str] | None = None) -> None:
    assert extra_args is None or len(extra_args) == 0
    tasks = TaskFile.from_file(arguments.task_file)

    result = run(
        arguments.output,
        tasks,
        arguments.with_tag,
        arguments.without_tag,
        arguments.only_tags,
        arguments.limit,
        arguments.random,
    )
    print(f"Returned {len(result.tasks)} of {len(tasks.tasks)} tasks.")


def main() -> None:
    run_ns(mk_parser().parse_args())

import argparse
import itertools
import random
from collections.abc import Iterator
from pathlib import Path
from typing import Any

from rocq_pipeline.task_modifiers import task_mod
from rocq_pipeline.task_modifiers.task_mod import TaskModifier
from rocq_pipeline.tasks import Project, Task, TaskFile


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
    parser.add_argument(
        "--add-mod",
        action="append",
        type=task_mod.of_string,
        help="Add a task modifier to a task",
    )
    parser.add_argument(
        "--rename",
        type=str,
        help="Rename the task. (Use $N to refer to the original task name, $I to refer to the id)",
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


def modify(
    t: Task, add_mods: list[TaskModifier] | None = None, rename: str | None = None
) -> Task:
    if add_mods:
        t.modifiers += add_mods
    if rename is not None:
        t.name = rename.replace("$N", t.name if t.name else t.get_id()).replace(
            "$I", t.get_id()
        )
        if t.name == "":
            t.name = None
    return t


def run(
    output: Path,
    tasks: TaskFile,
    with_tags: set[str] | None = None,
    without_tags: set[str] | None = None,
    only_tags: str | None = None,
    limit: int | None = None,
    random_selection: bool = False,
    rename: str | None = None,
    add_mods: list[TaskModifier] | None = None,
) -> TaskFile:
    """Filter the tasks in the TaskFile."""

    def norm(ts: set[str] | None) -> list[str]:
        if ts is None:
            return []
        else:
            return [tag for tag in ts if tag != ""]

    with_tags_l = norm(with_tags)
    without_tags_l = norm(without_tags)

    def keep(task: Task) -> bool:
        return eval_options(task.get_tags(), with_tags_l, without_tags_l, only_tags)

    filtered_tasks: Iterator[tuple[Project, Task]] = (
        (
            proj,
            modify(task, add_mods=add_mods, rename=rename),
        )
        for proj, task in tasks.iter_tasks()
        if keep(task)
    )

    # # Filter tasks within each bundle to preserve project associations
    # filtered_bundles: list[tuple[Project, list[Task]]] = []
    # all_filtered_tasks: list[Task] = []

    # for bundle in tasks.bundles:
    #     bundle_filtered = [task for task in bundle.tasks if keep(task)]
    #     if bundle_filtered:
    #         filtered_bundles.append((bundle.project, bundle_filtered))
    #         all_filtered_tasks.extend(bundle_filtered)

    # Apply limit across all tasks if specified
    if limit is not None:
        if random_selection:
            filtered_list = list(filtered_tasks)
            if len(filtered_list) > limit:
                selected_tasks = random.sample(filtered_list, limit)
                filtered_tasks = iter(selected_tasks)
            else:
                filtered_tasks = iter(filtered_list)
        else:
            # Take first N tasks across all bundles
            filtered_tasks = itertools.islice(filtered_tasks, 0, limit)

    result = TaskFile.from_tasks(filtered_tasks)
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
        add_mods=arguments.add_mod,
        rename=arguments.rename,
    )
    result_count = len(list(result.iter_tasks()))
    original_count = len(list(tasks.iter_tasks()))
    print(f"Returned {result_count} of {original_count} tasks.")


def main() -> None:
    run_ns(mk_parser().parse_args())

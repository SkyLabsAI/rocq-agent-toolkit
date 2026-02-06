import argparse
from pathlib import Path

from observability import get_logger

import rocq_pipeline.tasks as Tasks

logger = get_logger("task_runner")


def load_tasks(
    arguments: argparse.Namespace,
) -> tuple[str, list[tuple[Tasks.Project, Tasks.Task]]]:
    """Load the tasks from the command line arguments."""
    if arguments.task_json and arguments.task_file:
        logger.warning(
            " ".join(
                [
                    "[--task-file ...] and [--task-json ...] shouldn't both be used;",
                    "choosing [--task-json].",
                ]
            )
        )

    if arguments.task_json is not None:
        # TODO: Confirm that this is the correct setup
        tasks = arguments.task_json
        if not isinstance(tasks, list):
            tasks = [tasks]
        tasks = [Tasks.Task.model_validate(t) for t in tasks]
        project = Tasks.Project(name="tasks", git_url="", git_commit="", path=Path("."))
        return ("tasks", [(project, task) for task in tasks])
    elif arguments.task_file is not None:
        taskfile = Tasks.TaskFile.from_file(arguments.task_file)
        tasks_name = arguments.task_file.stem
        return (tasks_name, list(taskfile.iter_tasks()))
    else:
        raise ValueError(
            "Unspecified task.\nUse '--task-json ...literal-json...' or '--task-file path/to/task/file.{json,yaml}'."
        )

from argparse import ArgumentParser, Namespace
from pathlib import Path
from typing import Any

from rocq_pipeline.tasks import TaskFile


def mk_parser(parent: Any | None = None) -> ArgumentParser:
    """Used in ./cli.py to expose a 'build-deps' subcommand of 'rat'."""
    description = "Enumerate .vo build targets relative to cwd for a single task_file."
    help = "Supply a path to a single task file and enumerate its .vo dependencies relative to cwd."
    if parent:
        parser = parent.add_parser("build-deps", description=description, help=help)
    else:
        parser = ArgumentParser(description=description)
    parser.add_argument("task_file", type=Path, help="The path to a single task file")
    return parser


def run_ns(arguments: Namespace, extra_args: list[str] | None = None) -> None:
    """Used in ./cli.py to expose a 'build-deps' subcommand of 'rat'."""
    assert extra_args is None or len(extra_args) == 0
    taskfile = TaskFile.from_file(arguments.task_file)
    print(" ".join([str(vo_path) for vo_path in taskfile.build_deps()]))

from argparse import ArgumentParser, Namespace
from collections.abc import Callable
from typing import Any

from rocq_pipeline import find_tasks, service_cli, task_manip, task_runner, tracer
from rocq_pipeline.args_util import split_args

# TODO: cleanup these type annotations
#
# NOTE: argparser commands use some private types (e.g. [_SubParsersAction])
type mk_parserT[PARSER] = Callable[[Any | None], Any]
type run_nsT = Callable[[Namespace, list[str] | None], Any]
_entrypoints: dict[str, tuple[mk_parserT[Any], run_nsT]] = {
    "ingest": (find_tasks.mk_parser, find_tasks.run_ns),
    "run": (
        lambda subparsers: task_runner.mk_parser(subparsers, with_agent=True),
        task_runner.run_ns,
    ),
    "trace": (tracer.mk_parser, tracer.run_ns),
    "filter": (
        task_manip.mk_parser,
        task_manip.run_ns,
    ),
    "service": (service_cli.mk_service_parser, service_cli.service_run_ns),
    "dashboard": (service_cli.mk_dashboard_parser, service_cli.dashboard_run_ns),
}


# --- Entry Point ---
def main() -> None:
    parser = ArgumentParser(description="The Rocq Agent Toolkit Driver")
    subparsers = parser.add_subparsers(dest="command", help="Available commands")
    for mk_parser, _ in _entrypoints.values():
        mk_parser(subparsers)

    args, extra_args = split_args()
    arguments: Namespace = parser.parse_args(args)

    if arguments.command is None:
        parser.print_help()
    elif arguments.command in _entrypoints:
        [_, run_ns] = _entrypoints[arguments.command]
        run_ns(arguments, extra_args)
    else:
        parser.print_help()

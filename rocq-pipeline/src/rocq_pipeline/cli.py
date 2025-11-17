import sys
from argparse import ArgumentParser, Namespace

from rocq_pipeline import find_tasks, task_runner, tracer


# --- Entry Point ---
def main() -> None:
    parser = ArgumentParser(description="The Rocq Agent Toolkit Driver")
    subparsers = parser.add_subparsers(dest="command", help="Available commands")
    find_tasks.mk_parser(subparsers)
    task_runner.mk_parser(subparsers, with_agent=True)
    tracer.mk_parser(subparsers)
    args = sys.argv[1:]
    extra_args:list[str] = []
    try:
        idx = args.index('--')
        extra_args = args[idx+1:]
        args = args[:idx]
    except ValueError:
        pass

    arguments:Namespace = parser.parse_args(args)
    if arguments.command is None:
        parser.print_help()
    elif arguments.command == 'ingest':
        find_tasks.run_ns(arguments, extra_args)
    elif arguments.command == 'run':
        task_runner.run_ns(arguments, extra_args)
    elif arguments.command == 'trace':
        tracer.run_ns(arguments, extra_args)
    else:
        parser.print_help()

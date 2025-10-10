import argparse
from typing import override
from rocq_pipeline.agent import GiveUp
from rocq_pipeline.auto_agent import AutoAgent
import json
from rocq_pipeline import locator
from rocq_doc_manager import RocqDocManager

import sys

# def dune_rule(filename: str):
#     result = subprocess.run(["dune", "rule", f"{filename}o"], capture_output=True, text=True)
#     rule = sexpdata.loads(result.stdout)
#     action = None
#     for x in rule:
#         if x[0] == sexpdata.Symbol('action'):
#             action = x[1]
#             break
#     to_dir = '/home/gmalecha/skylabs/main' # workspace directory
#     args = []
#     if action[0] == sexpdata.Symbol('chdir'):
#         to_dir = f"{to_dir}/{action[1]}"
#         action = action[2]
#     if action[0] == sexpdata.Symbol('run'):
#         args = ["" + x for x in action[2:-1]]
#     filename = os.path.relpath(filename, to_dir)
#     print(f"filename = {filename}\nto_dir={to_dir}")
#     # args.remove("-boot") # rocq-doc-manager does not work with -boot
#     return RocqDocManager(args, filename, to_dir)

def build_rdm(filename: str):
    return RocqDocManager([], filename, dune=True)

# def doc_manager_for_task(task):
#     if

def task_main(agent_type, args = None) -> bool:
    """
    Run the given agent on the task.
    `agent_type` is the type of the agent, i.e. the class to instantiate.
    e.g. `Agent` or `AutoAgent`.
    """
    if args is None:
        args = sys.argv[1:]

    # Set up the argument parser
    parser = argparse.ArgumentParser(
        description="Parses a file name, an optional trace flag, and collects all arguments following a '--' separator.",
        epilog="Example usage:\n  python proof_driver.py [--trace] proof.v [-- Rocq parameters]"
    )
    # Add the single required positional argument
    parser.add_argument(
        '--task-json',
        type=str,
        help='The task descriptor, as JSON.'
    )
    parser.add_argument(
        '--task-file',
        type=str,
        help='The task descriptor in a file, JSON or YAML'
    )
    # Add the optional --trace flag
    parser.add_argument(
        '--trace',
        action='store_true',
        help='Enable tracing.'
    )

    # Allow the agent to set up additional arguments
    # TODO: if this function is not defined, then it shouldn't
    # do anything
    if hasattr(agent_type, "arg_parser"):
        agent_type.arg_parser(parser)

    arguments = parser.parse_args(args)

    task = None
    if not arguments.task_json is None:
        assert arguments.task_file is None
        task = json.loads(arguments.task_json)
    elif not arguments.task_file is None:
        if arguments.task_file.endswith('.yml') or arguments.task_file.endswith('.yaml'):
            print("yaml files not yet supported")
            return False
        elif arguments.task_file.endswith('.json'):
            with open(arguments.task_file, 'r') as tf:
                task = json.load(tf)
        else:
            print("unrecognized task descriptor")
            return False
    else:
        print("unspecified task")
        return False

    rdm = build_rdm(task['file'])
    rdm.load_file()
    if not locator.parse_locator(task['locator'])(rdm):
        print("locator returned false")
        return False

    if hasattr(agent_type, "build"):
        # TODO: should we remove any attributes from the task
        agent = agent_type.build(prompt=task['prompt'] if 'prompt' in task else None)
    else:
        agent = agent_type()

    try:
        agent.run(rdm)
        print("task completed")
    except GiveUp as e:
        print(f"agent gave up with message: {e.message}")
    return True

if __name__ == '__main__':
    task_main(AutoAgent)

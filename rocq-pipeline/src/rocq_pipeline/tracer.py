import argparse
import json
from pathlib import Path
from typing import Any

from rocq_doc_manager import DuneUtil, RocqDocManager

import rocq_pipeline.tasks as Tasks
from rocq_pipeline import find_tasks, locator, util
from rocq_pipeline.extractor import BeforeAndAfter, GoalAsString, TacticExtractor


def trace_proof[T](extractor: TacticExtractor[T], rdm: RocqDocManager) -> list[tuple[(T|None), str, (T|None)]]:
    try:
        tactics = find_tasks.scan_proof(rdm.doc_suffix()).proof_tactics
        trace: list[tuple[(T|None),str,(T|None)]] = []
        for tactic in tactics:
            pre = extractor.before(rdm, tactic)
            rdm.run_command(tactic)
            post = extractor.after(rdm, tactic)
            trace.append((pre, tactic.strip(".").strip(), post))
        return trace
    except Exception:
        return []

def mk_parser(parent: Any|None=None) -> Any:
    # Set up the argument parser
    if parent:
        parser = parent.add_parser("trace", help="Traces Rocq states")
    else:
        parser = argparse.ArgumentParser(description="Traces Rocq states.")

    # Add the single required positional argument
    parser.add_argument("--task-json", type=json.loads, help="The task descriptor, as JSON.")
    parser.add_argument(
        "--task-file", type=Path, help="The task descriptor in a file, JSON or YAML"
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("."),
        help="The directory to output task results, as JSON."
    )
    parser.add_argument(
        "-j", "--jobs",
        type=lambda N: max(1, int(N)),
        default=1,
        help="The number of parallel workers."
    )
    return parser


def run(output_dir: Path, wdir:Path, tasks: list[Tasks.Task], jobs:int=1) -> None:
    def run_task(task: Tasks.Task, progress: util.ProgressCallback) -> bool:
        # TODO: find a better ID for tasks
        task_id: str = Tasks.get_task_id(task)
        output_file: Path = output_dir / f"{task_id.replace('/','_').replace('#','_')}.json"

        try:
            task_file: Path = wdir / task["file"]
            with RocqDocManager(
                    DuneUtil.rocq_args_for(task_file),
                    str(task_file),
                    dune=True,
            ).sess() as rdm:
                progress(0.01, "🔃")
                load_reply = rdm.load_file()
                progress(0.05, "🔃")
                if isinstance(load_reply, RocqDocManager.Err):
                    raise RuntimeError(" ".join([
                        f"rocq-doc-manager failed to load {task_file};",
                        "is the [rocq-doc-manager] executable available",
                        "and has the file been built?"
                    ]))

                if not locator.parse_locator(task["locator"])(rdm):
                    print(f"Failed to find task: {task_id}")
                    return False
                progress(0.1, "💭")

                trace = trace_proof(BeforeAndAfter(GoalAsString()), rdm)
                progress(0.95, "💭")

            with open(output_file, "w") as output:
                json.dump(trace, output)

            return True

        except Exception:
            return False

    util.parallel_runner(run_task, [(Tasks.get_task_id(x), x) for x in tasks], lambda x: x, jobs=jobs)

def run_ns(arguments: argparse.Namespace, extra_args:list[str]|None=None) -> bool:
    assert extra_args is None or len(extra_args) == 0
    if arguments.task_json and arguments.task_file:
        print(" ".join([
            "[--task-file ...] and [--task-json ...] shouldn't both be used;",
            "choosing [--task-json]."
        ]))
    if arguments.task_json is not None:
        # TODO: if we had a schema we could automatically validate that the
        # task JSON has the expected shape.
        tasks = Tasks.mk_validated_tasklist(arguments.task_json)
        wdir = Path('.')
    elif arguments.task_file is not None:
        (wdir, tasks) = Tasks.load_tasks(arguments.task_file)
    else:
        print("unspecified task")
        return False

    run(arguments.output, wdir, tasks)
    return True

def main() -> bool:
    arguments = mk_parser().parse_args()
    return run_ns(arguments)

if __name__ == '__main__':
    main()

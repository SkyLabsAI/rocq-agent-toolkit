import argparse
import json
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any

from rocq_doc_manager import DuneUtil, RocqDocManager

import rocq_pipeline.tasks as Tasks
from rocq_pipeline import find_tasks, locator


class StateExtractor[T]:
    """
    A StateExtractor extracts state from a Rocq proof.
    """
    def __call__(self, rdm: RocqDocManager) -> T | None:
        """
        Extract a feature from the current state.
        """
        return None

class AllStateExtractor(StateExtractor[dict[str,Any]]):
    """
    Produce an object that contains the results of all of the state extractors
    """
    def __init__(self, extractors: dict[str, StateExtractor[Any]]):
        self._extractors:dict[str, StateExtractor] = extractors

    def __call__(self, rdm: RocqDocManager) -> dict[str,Any]:
        result: dict[str, Any] = {}
        for (k,extract) in self._extractors.items():
            # TODO: for now, we assume that extractors are hygeinic in the sense that they do revert any effects they might have on the document.
            # In the future, we could use the revert environment to enforce this.
            try:
                k_result = extract(rdm)
                if k_result is not None:
                    result[k] = k_result
            except Exception:
                pass
        return result

class GoalAsString(StateExtractor[str]):
    """A simple extractor that just gets the current goal the way it is printed in Rocq."""
    def __call__(self, rdm: RocqDocManager) -> str:
        result = rdm.current_goal()
        if isinstance(result, rdm.Resp):
            return result.result # type: ignore
        return ""

def trace_proof[T](extractor: StateExtractor[T], rdm: RocqDocManager) -> list[tuple[(T|None), str, (T|None)]]:
    try:
        tactics = find_tasks.scan_proof(rdm.doc_suffix()).proof_tactics
        trace: list[tuple[(T|None),str,(T|None)]] = []
        for tactic in tactics:
            pre = extractor(rdm)
            rdm.run_command(tactic)
            post = extractor(rdm)
            trace.append((pre, tactic.strip(".").strip(), post))
        return trace
    except Exception:
        return []

def mk_argparser() -> argparse.ArgumentParser:
    # Set up the argument parser
    parser = argparse.ArgumentParser(
        description="Traces Rocq states.",
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
        help="The directory to output task results, as JSON."
    )
    parser.add_argument(
        "-j", "--jobs",
        type=lambda N: max(1, int(N)),
        default=1,
        help="The number of parallel workers."
    )
    return parser

def main(args: list[str] | None = None) -> bool:
    """
    The entry point to the tracer
    """
    if args is None:
        args = sys.argv[1:]

    arguments = mk_argparser().parse_args(args)

    wdir = Path(".")

    if arguments.task_json and arguments.task_file:
        print(" ".join([
            "[--task-file ...] and [--task-json ...] shouldn't both be used;",
            "choosing [--task-json]."
        ]))

    if arguments.task_json is not None:
        # TODO: if we had a schema we could automatically validate that the
        # task JSON has the expected shape.
        tasks = Tasks.mk_validated_tasklist(arguments.task_json)
    elif arguments.task_file is not None:
        (wdir, tasks) = Tasks.load_tasks(arguments.task_file)
    else:
        print("unspecified task")
        return False

    def rocq_args(filename: Path) -> list[str]:
        # TODO: a better default
        return DuneUtil.rocq_args_for(filename)

    def run_task(task: dict[str, Any]) -> bool:
        # TODO: find a better ID for tasks
        task_id: str = f"{task['file']}#{task['locator']}"

        try:
            task_file: Path = wdir / task["file"]
            with RocqDocManager(
                    rocq_args(task_file),
                    str(task_file),
                    dune=True,
            ) as rdm:
                load_reply = rdm.load_file()
                if isinstance(load_reply, RocqDocManager.Err):
                    raise RuntimeError(" ".join([
                        f"rocq-doc-manager failed to load {task_file};",
                        "is the [rocq-doc-manager] executable available",
                        "and has the file been built?"
                    ]))

                if not locator.parse_locator(task["locator"])(rdm):
                    print(f"{task_id}: locator returned false")
                    return False

                trace = trace_proof(GoalAsString(), rdm)

            with open(arguments.output_dir / f"{task_id.replace('/','_')}.json", "w") as output:
                json.dump(trace, output)

            return True

        except Exception:
            return False

    with ThreadPoolExecutor(arguments.jobs) as tpe:
        # NOTE: iterator blocks if the next result has not been yielded
        for result in tpe.map(run_task, tasks):
            print(f"Finished task: {result}")
            pass

    return True

if __name__ == '__main__':
    main()

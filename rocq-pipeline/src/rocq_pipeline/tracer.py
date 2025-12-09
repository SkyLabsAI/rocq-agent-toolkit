import argparse
import itertools
import json
from pathlib import Path
from typing import Any

from rocq_doc_manager import DuneUtil, RocqDocManager

import rocq_pipeline.tasks as Tasks
from rocq_pipeline import find_tasks, loader, locator, rocq_args, util
from rocq_pipeline.tracers.extractor import (
    BeforeAndAfter,
    TacticExtractor,
    TacticExtractorBuilder,
)
from rocq_pipeline.tracers.json_goal import JsonGoal


def trace_proof[T](
    extractor: TacticExtractor[T],
    rdm: RocqDocManager,
    progress: util.ProgressCallback,
    progress_min: float = 0.0,
    progress_max: float = 1.0,
) -> list[tuple[(T | None), str, (T | None)]]:
    tactics = find_tasks.scan_proof(rdm.doc_suffix()).proof_tactics
    extractor.start_proof(rdm)
    trace: list[tuple[(T | None), str, (T | None)]] = []
    step_size: float = (progress_max - progress_min) / len(tactics)
    for i, tactic in enumerate(tactics):
        pre = extractor.before(rdm, tactic)
        progress.status(status=tactic[:10])
        assert not isinstance(rdm.run_command(tactic), rdm.Err)
        progress.status(percent=progress_min + i * step_size)
        post = extractor.after(rdm, tactic)
        trace.append((pre, tactic.strip(".").strip(), post))
    return trace


def mk_parser(parent: Any | None = None, with_tracer: bool = True) -> Any:
    # Set up the argument parser
    if parent:
        parser = parent.add_parser("trace", help="Traces Rocq states")
    else:
        parser = argparse.ArgumentParser(description="Traces Rocq states.")

    # Add the single required positional argument
    parser.add_argument(
        "--task-json", type=json.loads, help="The task descriptor, as JSON."
    )
    parser.add_argument(
        "--task-file", type=Path, help="The task descriptor in a file, JSON or YAML"
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("."),
        help="The directory to output task results, as JSON.",
    )
    if with_tracer:
        parser.add_argument(
            "--tracer", type=str, help="The tracer to use specified as: file.py:def."
        )
    parser.add_argument(
        "-j",
        "--jobs",
        type=lambda N: max(1, int(N)),
        default=1,
        help="The number of parallel workers.",
    )
    return parser


def run(
    tracer_builder: TacticExtractorBuilder,
    output_dir: Path,
    wdir: Path,
    tasks: list[Tasks.Task],
    jobs: int = 1,
) -> None:
    output_dir.mkdir(exist_ok=True)
    if not output_dir.is_dir():
        print(f"No such output directory: {output_dir}")

    def run_task(task: Tasks.Task, progress: util.ProgressCallback) -> bool:
        # TODO: find a better ID for tasks
        task_id: str = Tasks.get_task_id(task)
        output_file: Path = (
            output_dir / f"{task_id.replace('/', '_').replace('#', '_')}.json"
        )

        try:
            tracer = tracer_builder.build()
            extra_paths = itertools.chain.from_iterable(
                (["-Q", str(v), k] for k, v in tracer.extra_paths().items())
            )

            task_file: Path = wdir / task["file"]
            with RocqDocManager(
                rocq_args.extend_args(
                    DuneUtil.rocq_args_for(task_file), list(extra_paths)
                ),
                str(task_file),
                dune=True,
            ).sess(load_file=True) as rdm:
                tracer.setup(rdm)
                progress.status(0.05, "🔃")

                if not locator.parse_locator(task["locator"])(rdm):
                    print(f"Failed to find task: {task_id}")
                    return False
                progress.status(0.1, "💭")

                trace = trace_proof(tracer, rdm, progress, 0.1, 0.95)
                progress.status(0.95, "💭")

            with open(output_file, "w") as output:
                json.dump(trace, output)
            progress.status(1)

            return True
        except Exception as err:
            print(f"Failed at task {task_id}.{err}")
            return False

    util.parallel_runner(
        run_task, [(Tasks.get_task_id(x), x) for x in tasks], lambda x: x, jobs=jobs
    )


def run_ns(arguments: argparse.Namespace, extra_args: list[str] | None = None) -> bool:
    assert extra_args is None or len(extra_args) == 0
    if arguments.task_json and arguments.task_file:
        print(
            " ".join(
                [
                    "[--task-file ...] and [--task-json ...] shouldn't both be used;",
                    "choosing [--task-json].",
                ]
            )
        )
    if arguments.task_json is not None:
        # TODO: if we had a schema we could automatically validate that the
        # task JSON has the expected shape.
        tasks = Tasks.mk_validated_tasklist(arguments.task_json)
        wdir = Path(".")
    elif arguments.task_file is not None:
        (wdir, tasks) = Tasks.load_tasks(arguments.task_file)
    else:
        print("unspecified task")
        return False

    if arguments.tracer is None:
        tracer: TacticExtractorBuilder = TacticExtractorBuilder.of_tactic_extractor(
            lambda: BeforeAndAfter(JsonGoal())
        )  # GoalAsString())
    else:
        if isinstance(arguments.tracer, str):
            tracer = loader.load_from_str(arguments.tracer)
        else:
            tracer = arguments.tracer

        # if isinstance(tracer, TacticExtractorBuilder):
        #     print("ok")
        #     tracer = BeforeAndAfter(tracer)
        # elif not isinstance(tracer, TacticExtractor):
        #     # print(f"'{arguments.tracer}' is a '{tracer}' but expected a [TacticExtractor].")
        #     return False

    run(tracer, arguments.output_dir, wdir, tasks, jobs=arguments.jobs)
    return True


def tracer_main(tracer: TacticExtractor[Any], args: list[str] | None = None) -> bool:
    """
    This function can be used to create a `main` entry point for a specific tracer.
    Use it with something like:

    ```python
    my_tracer = ...
    if __name__ == '__main__':
        rocq_pipeline.tracer.tracer_main(my_tracer)
    ```
    """
    arguments = mk_parser().parse_args(args)
    arguments.tracer = tracer
    return run_ns(arguments)


def main() -> bool:
    arguments = mk_parser().parse_args()
    return run_ns(arguments)


if __name__ == "__main__":
    main()

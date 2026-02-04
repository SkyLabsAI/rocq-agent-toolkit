import argparse
import itertools
import json
import traceback
from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from typing import Any, cast

from rocq_doc_manager import DuneUtil, RocqCursor, RocqDocManager
from rocq_doc_manager import rocq_doc_manager_api as api

import rocq_pipeline.tasks as Tasks
from rocq_pipeline import find_tasks, loader, rocq_args, util
from rocq_pipeline.args import load_tasks
from rocq_pipeline.tracers import json_goal
from rocq_pipeline.tracers.extractor import (
    Tracer,
)


def trace_proof(
    tracer: Tracer[dict[str, Any]],
    rdm: RocqCursor,
    progress: util.ProgressCallback,
    progress_min: float = 0.0,
    progress_max: float = 1.0,
) -> list[dict[str, Any]]:
    tactics = find_tasks.scan_proof(rdm.doc_suffix()).proof_tactics
    tracer.start_proof(rdm)
    trace = []
    step_size: float = (progress_max - progress_min) / len(tactics)
    for i, tactic in enumerate(tactics):
        after = tracer.before_internal(rdm, tactic)
        progress.status(status=tactic[:10])
        assert not isinstance(rdm.run_command(tactic), api.Err)
        progress.status(percent=progress_min + i * step_size)
        if after is not None:
            result = after(rdm, tactic)
            if result is not None:
                if "tactic" not in result:
                    result["tactic"] = tactic.strip(".").strip()
                trace.append(result)
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
            "--tracer",
            type=str,
            help="The tracer to use. The argument is interpreted as follows: The forms [<path>/<module>.py:<func>] and [<package.path>.<module>:<func>] use [<module>.<func>()], whereas [<path>/<module>.py] and [<package.path>.<module>] use [<module>.build()].",
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
    tracer_builder: Callable[[], Tracer[Any]],
    output_dir: Path,
    tasks: list[tuple[Tasks.Project, Tasks.Task]],
    jobs: int = 1,
) -> None:
    output_dir.mkdir(exist_ok=True)
    if not output_dir.is_dir():
        print(f"No such output directory: {output_dir}")

    def run_task(
        proj_task: tuple[Tasks.Project, Tasks.Task], progress: util.ProgressCallback
    ) -> bool:
        project, task = proj_task
        # TODO: find a better ID for tasks
        task_id: str = task.get_id()
        output_file: Path = (
            output_dir / f"{task_id.replace('/', '_').replace('#', '_')}.json"
        )

        try:
            tracer = tracer_builder()
            extra_paths = itertools.chain.from_iterable(
                (["-Q", str(v), k] for k, v in tracer.extra_paths().items())
            )

            task_file: Path = project.path / task.file
            with RocqDocManager(
                rocq_args.extend_args(
                    DuneUtil.rocq_args_for(task_file), list(extra_paths)
                ),
                str(task_file),
                dune=True,
            ).sess(load_file=True) as rdm:
                rc = rdm.cursor()
                tracer.setup(rc)
                progress.status(0.05, "🔃")

                if not task.locator(rc):
                    print(f"Failed to find task: {task_id}")
                    return False
                progress.status(0.1, "💭")

                trace = trace_proof(tracer, rc, progress, 0.1, 0.95)
                progress.status(0.95, "💭")

            with open(output_file, "w") as output:
                json.dump(trace, output)
            progress.status(1)

            return True
        except Exception as err:
            print(traceback.format_exc())
            print(f"Failed at task {task_id}.{err}")
            return False

    util.parallel_runner(
        run_task,
        [(f"{t[0].get_id()}#{t[1].get_id()}", t) for t in tasks],
        lambda x: x,
        jobs=jobs,
    )


def run_ns(arguments: argparse.Namespace, extra_args: list[str] | None = None) -> bool:
    assert extra_args is None or len(extra_args) == 0
    _, tasks = load_tasks(arguments)

    if arguments.tracer is None:

        def tracer() -> Tracer[Any]:
            return json_goal.build()
    else:
        if isinstance(arguments.tracer, str):
            loaded = loader.load_from_str(arguments.tracer)
            if isinstance(loaded, ModuleType):
                tracer = loaded.build
            else:
                assert callable(loaded), (
                    f"Object found at {arguments.tracer} is not callable. Its value is: {repr(loaded)}"
                )
                tracer = cast(Callable[[], Tracer[Any]], loaded)
        else:
            tracer = arguments.tracer

        # if isinstance(tracer, TacticExtractorBuilder):
        #     print("ok")
        #     tracer = BeforeAndAfter(tracer)
        # elif not isinstance(tracer, TacticExtractor):
        #     # print(f"'{arguments.tracer}' is a '{tracer}' but expected a [TacticExtractor].")
        #     return False

    run(
        tracer,
        arguments.output_dir,
        tasks,
        jobs=arguments.jobs,
    )
    return True


def tracer_main(tracer: Tracer[Any], args: list[str] | None = None) -> bool:
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

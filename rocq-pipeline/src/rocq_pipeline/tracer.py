import argparse
import json
import traceback
from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from typing import Any, cast

import rocq_ltac_interp as ltac_interp
from pydantic import BaseModel, Field, JsonValue
from rocq_doc_manager import RocqCursor, rc_sess
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_dune_util import rocq_args_for
from rocq_ltac_interp.tacinterp import LtacFail, RunCommandResult

import rocq_pipeline.tasks as Tasks
from rocq_pipeline import find_tasks, loader, util
from rocq_pipeline.args import load_tasks
from rocq_pipeline.tracers import json_goal, string_goal
from rocq_pipeline.tracers.extractor import (
    AllTracer,
    InteractionTrace,
    MapTracer,
    OutputDict,
    Tracer,
    pivot_output_dict,
)
from rocq_pipeline.with_deps import rocq_deps_for


class TraceConfig(BaseModel):
    subtactic: bool = Field(
        description="Break aggregate tactics, e.g. `intros; apply x` into atomic tactics.",
        default=False,
    )


async def trace_proof(
    tracer: Tracer[OutputDict[JsonValue]],
    rc: RocqCursor,
    *,
    progress: util.ProgressCallback | None = None,
    config: TraceConfig | None = None,
) -> list[InteractionTrace]:
    """Trace a proof."""
    config = config or TraceConfig()

    if config.subtactic:
        await ltac_interp.load(rc)

    prog: util.ProgressCallback = progress if progress else util.MockFeedback()
    tactics = find_tasks.scan_proof(await rc.doc_suffix()).proof_tactics
    await tracer.start_proof(rc)
    traces: list[InteractionTrace] = []

    if len(tactics) == 0:
        step_size = 0.0
    else:
        step_size = 1.0 / len(tactics)

    for i, tactic in enumerate(tactics):
        after = await tracer.start(rc, tactic)
        prog.status(status=tactic[:10])

        if config.subtactic:
            # TODO: this setup will not be enough because it
            # 1. is not tracking aggregate tactics
            # 2. it doesn't eliminate tactics that ultimately don't make progress
            # 3. it would be very convenient if the atomic runner already gave information
            #    about what goals where impacted
            async def run_atom(
                rc: RocqCursor,
                goal: int,
                tac: str,
                *,
                pre: rdm_api.ProofState,
                trace: int | None = None,
            ) -> RunCommandResult:
                # Note that that the tactic here does not have a `.`, but
                # the extractors expect tactics with `.`
                tac_with_period = f"{tac.strip()}."
                local_after = await tracer.start(rc, tac_with_period)
                result = await ltac_interp.tacinterp.run_tac(
                    rc, goal, tac, pre=pre, trace=trace
                )
                if local_after and (after := await local_after(rc, tac_with_period)):
                    nonlocal traces
                    traces.append(
                        InteractionTrace.of_output_dict(tac_with_period, after)
                    )
                return result

            async with (await rc.clone()).sess() as rc_local:
                try:
                    await ltac_interp.interp_tactic(rc_local, tactic, run_atom=run_atom)
                except ValueError:
                    # not a tactic
                    pass
                except NotImplementedError:
                    # These are best-effort
                    print(f"Not implemented: {tactic}")
                    pass
                except LtacFail:
                    # These are best-effort
                    pass

        run_command_result = await rc.run_command(tactic)
        if isinstance(run_command_result, rdm_api.Err):
            raise ValueError(
                f"Running tactic '{str(tactic)}' failed: {str(run_command_result)}"
            )

        prog.status(percent=i * step_size)
        if after is not None and (result := await after(rc, tactic)):
            traces.append(InteractionTrace.of_output_dict(tactic, result))
    await tracer.end_proof(rc)
    return traces


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
    parser.add_argument(
        "--fine-grained",
        dest="fine_grained",
        action="store_true",
        default=False,
        help="Trace individual tactics within a tactic, e.g. `intros; apply x` will trace `intros` and `apply x` independently.",
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
    *,
    config: TraceConfig | None = None,
    jobs: int = 1,
) -> None:
    output_dir.mkdir(exist_ok=True)
    if not output_dir.is_dir():
        print(f"No such output directory: {output_dir}")

    async def run_task(
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

            task_file: Path = project.path / task.file
            rocq_args = rocq_args_for(
                task_file, plugins=[ltac_interp.PLUGIN] + rocq_deps_for(tracer)
            )
            async with rc_sess(
                str(task_file),
                rocq_args=rocq_args,
                dune=True,
                load_file=True,
            ) as rc:
                await ltac_interp.load(rc)
                await tracer.setup(rc)
                progress.status(0.05, "🔃")

                if not await task.locator.go_to(rc):
                    print(f"Failed to find task: {task_id}")
                    return False
                progress.status(0.1, "💭")

                trace = await trace_proof(
                    tracer,
                    rc,
                    progress=util.DelimitedFeedback(progress, min=0.1, max=0.95),
                    config=config,
                )
                progress.status(0.95, "💭")

            with open(output_file, "w") as output:
                json.dump([m.model_dump() for m in trace], output)
            progress.status(1)

            return True
        except Exception as err:
            print(traceback.format_exc())
            print(f"Failed at task {task_id}.{err}")
            return False

    util.parallel_runner(
        run_task,
        [(f"{t[0].get_id()}#{t[1].get_id()}", t) for t in tasks],
        succeeded=lambda x: x,
        jobs=jobs,
    )


def run_ns(arguments: argparse.Namespace, extra_args: list[str] | None = None) -> bool:
    assert extra_args is None or len(extra_args) == 0
    _, tasks = load_tasks(arguments)

    if arguments.tracer is None:

        def tracer() -> Tracer[Any]:
            return MapTracer(
                AllTracer(
                    {
                        "json_goal": cast(
                            Tracer[OutputDict[JsonValue]], json_goal.build()
                        ),
                        "string_goal": cast(
                            Tracer[OutputDict[JsonValue]], string_goal.build()
                        ),
                    }
                ),
                pivot_output_dict,
            )
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
        config=TraceConfig(subtactic=arguments.fine_grained),
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

import argparse
import json
import os
import sys
import uuid
from argparse import ArgumentParser, Namespace
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from dotenv import load_dotenv
from observability import (
    LoggingConfig,
    add_log_context,
    get_logger,
    setup_logging,
)
from rocq_doc_manager import DuneUtil, RocqDocManager

import rocq_pipeline.tasks as Tasks
from rocq_pipeline import loader, locator, util
from rocq_pipeline import rocq_args as RocqArgs
from rocq_pipeline.agent import (
    AgentBuilder,
    AutoAgent,
    OneShotBuilder,
    TaskResult,
)
from rocq_pipeline.env_manager import Environment, EnvironmentRegistry
from rocq_pipeline.locator import Locator
from rocq_pipeline.schema import task_output

logger = get_logger("task_runner")

load_dotenv()


def init_logging(env: Environment) -> None:
    """Initialise logging based on the current environment and CLI flags.

    This is intentionally called from entrypoints *after* argument parsing
    so that ``--env`` can influence the OTLP endpoint.
    """
    otlp_endpoint = env.get_otlp_endpoint()
    log_config = LoggingConfig(
        service_name="rocq_agent",
        log_level=os.getenv("LOG_LEVEL", "INFO"),
        otlp_endpoint=env.get_otlp_endpoint(),
        enable_console_logging = os.getenv("ENABLE_CONSOLE_LOGGING", "false").lower() == "true",
        )
    setup_logging(log_config)
    logger.info("Logging configured with OTLP endpoint: %s", otlp_endpoint)


def mk_parser(parent: Any, with_agent: bool = True) -> Any:
    """
    Extend parent or build a fresh argument parser.
    """
    # Set up the argument parser
    desc = "Run an agent over a collection of tasks"
    if parent:
        parser = parent.add_parser("run", help=desc)
    else:
        parser = ArgumentParser(description=desc)

    if with_agent:
        parser.add_argument(
            "--agent",
            type=str,
            help="The agent builder as 'module_path:value', e.g. 'path/to/agent.py:default",
            required=True,
        )

    # Add the single required positional argument
    parser.add_argument(
        "--task-json", type=json.loads, help="The task descriptor, as JSON."
    )
    parser.add_argument(
        "--task-file", type=Path, help="The task descriptor in a file, JSON or YAML"
    )
    # Add the optional --trace flag
    parser.add_argument("--trace", action="store_true", help="Enable tracing.")
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("."),
        help="The directory to output task results, as JSONL.",
    )
    parser.add_argument(
        "-j",
        "--jobs",
        type=lambda N: max(1, int(N)),
        default=1,
        help="The number of parallel workers.",
    )

    # Add deployment mode flag
    parser.add_argument(
        "--env",
        type=str,
        default="none",
        help="Deployment environment (e.g., 'local', 'staging'). Default: none",
    )

    return parser


# def main(agent_type: type[Agent], args: list[str] | None = None) -> bool:
#     pass


@dataclass
class FullTask:
    id: str
    file: Path
    locator: Locator
    tags: set[str]
    rocq_args: list[str] | None
    prompt: str | None


def collect_env_tags(prefix: str = "TAG_") -> task_output.Tags:
    """
    Collect environment variables that represent tags.

    For each variable of the form TAG_FOO=bar, this returns an entry
    {"foo": "bar"} in the resulting dict.
    """
    tags: dict[str, str] = {}
    for key, value in os.environ.items():
        if key.startswith(prefix):
            tag_key = key[len(prefix):].lower()
            tags[tag_key] = value
    return task_output.Tags(tags)


def run_task(
    build_agent: AgentBuilder,
    task: FullTask,
    run_id: str,
    wdir: Path,
    tags: task_output.Tags,
    progress: util.ProgressCallback,
) -> task_output.TaskOutput | None:
    """
    Build an agent using [build_agent] and invoke it on the task.
    """
    # Add run_id to log context for this thread
    add_log_context("run_id", run_id)

    task_id: str = task.id
    add_log_context("task_id", task_id)
    # TODO: integrate with opentelemetry, properly instrument the agent
    # framework and derived agents
    trace_id: str | None = None
    timestamp_iso_8601 = datetime.now(UTC).isoformat()

    task_result: TaskResult | None = None
    agent = build_agent(task.prompt)

    try:
        task_file = task.file
        progress.status(0.01, "🔃")
        rocq_args = (
            RocqArgs.extend_args(DuneUtil.rocq_args_for(task_file), build_agent.extra_rocq_args())
            if task.rocq_args is None
            else task.rocq_args
        )
        with RocqDocManager(
            rocq_args,
            str(task_file),
            dune=True,
        ).sess(load_file=True) as rdm:
            progress.status(0.05, "🔃")
            if not task.locator(rdm):
                progress.log(f"{task_id}: locator returned false")
                return None
            progress.status(0.1, "💭")
            task_result = agent.run(rdm)
    except Exception as e:
        progress.log(f"Failure with {e}")
        task_result = TaskResult.from_exception(e)
    finally:
        progress.status(0.95, "🔚")
    assert task_result is not None

    # Log the result
    if not task_result.success:
        progress.log(f"{agent.name()} gave up with message: {task_result.message}")
    else:
        progress.log(f"task completed: {task_result.message}")

    # For the time being taking id from the environment variable
    # TODO: Update it to add automatically
    # can be created based on the task input path
    # or in a way that it can detect the changes in the task input path or dataset.
    dataset_id = os.getenv("DATASET_NAME", "default")

    for task_tag in task.tags:
        tags.value.update({f"TASK_{task_tag}": task_tag})

    return task_result.to_task_output(
        run_id=run_id,
        task_kind=task.locator.task_kind(),
        task_id=task_id,
        dataset_id=dataset_id,
        timestamp_utc=timestamp_iso_8601,
        agent_name=agent.name(),
        trace_id=trace_id,
        metadata=task_output.Metadata(tags=tags),
    )


def load_tasks(arguments: argparse.Namespace) -> tuple[str, Path, list[FullTask]]:
    """
    The path returned here is used to find the build.py file.
    TODO: That should be resolved in here
    """
    if arguments.task_json and arguments.task_file:
        logger.warning(
            " ".join(
                [
                    "[--task-file ...] and [--task-json ...] shouldn't both be used;",
                    "choosing [--task-json].",
                ]
            )
        )

    def to_full_task(raw: Tasks.Task, wdir: Path) -> FullTask:
        # TODO: find a better name for tasks
        id = Tasks.get_task_id(raw)
        file = wdir / raw["file"]
        tags: set[str] = Tasks.get_task_tags(raw)
        return FullTask(
            id,
            file,
            locator.parse_locator(raw["locator"]),
            tags,
            None,
            raw["prompt"] if "prompt" in raw else None,
        )

    if arguments.task_json is not None:
        tasks = Tasks.mk_validated_tasklist(arguments.task_json)
        wdir = Path(".")
        return ("tasks", wdir, [to_full_task(raw, wdir) for raw in tasks])
    elif arguments.task_file is not None:
        (wdir, tasks) = Tasks.load_tasks(arguments.task_file)
        tasks_name = arguments.task_file.stem
        return (tasks_name, wdir, [to_full_task(raw, wdir) for raw in tasks])
    else:
        raise ValueError("unspecified task")


def load_agent(agent_desc: str) -> AgentBuilder:
    try:
        agent_builder = loader.load_from_str(agent_desc, "dyn_loaded_agent")
        if isinstance(agent_builder, AgentBuilder):
            return agent_builder
        raise Exception(f"{agent_builder} is not an [AgentBuilder]")
    except Exception as err:
        raise ValueError(f"Failed to load AgentBuilder from {agent_desc}.") from err

@dataclass
class RunConfiguration:
    agent_builder: AgentBuilder
    tasks: list[FullTask]
    tasks_name: str
    output_dir: Path
    working_dir: Path
    trace: bool
    jobs: int
    tags: task_output.Tags
    deployment_env: Environment | None = None


def parse_arguments(
    arguments: Namespace, agent_builder: AgentBuilder | None = None
) -> RunConfiguration:
    if agent_builder is None:
        if arguments.agent is None:
            raise ValueError("Missing agent configuration. Pass [--agent ...].")
        agent_builder = load_agent(arguments.agent)

    (tasks_name, wdir, tasks) = load_tasks(arguments)

    # Get deployment environment
    env_name = getattr(arguments, "env", "none")
    env_cls = EnvironmentRegistry.get(env_name)
    deployment_env = env_cls()

    init_logging(deployment_env)

    tags = collect_env_tags()
    return RunConfiguration(
        agent_builder,
        tasks,
        tasks_name,
        arguments.output_dir,
        wdir,
        arguments.trace,
        arguments.jobs,
        tags,
        deployment_env,
    )


def run_config(config: RunConfiguration) -> bool:
    # Setup environment based on deployment mode
    if config.deployment_env:
        logger.info(f"Setting up environment: {type(config.deployment_env).__name__}")

        if not config.deployment_env.setup():
            logger.error("Failed to setup environment")
            return False

    now_str = datetime.now().strftime("%Y%m%d_%H%M")
    tasks_result_file: Path = (
        config.output_dir / f"{config.tasks_name}_results_{now_str}.jsonl"
    )
    run_id: str = str(uuid.uuid4())
    # Here log context is not getting passed in the multithreads
    # # add_log_context("run_id", run_id)

    def run_it(full_task: FullTask, progress: Any) -> task_output.TaskOutput | None:
        return run_task(
            config.agent_builder,
            full_task,
            run_id,
            wdir=config.working_dir,
            tags=config.tags,
            progress=progress,
        )

    # Touch the file early to make sure that it is createable
    Path(tasks_result_file).touch()

    def is_success(result: task_output.TaskOutput | None) -> bool:
        return result is not None and str(result.status.value.kind) == "Success"

    def succeeded(result: task_output.TaskOutput | None) -> bool:
        if result is None:
            return False
        with open(tasks_result_file, "a", encoding="utf8") as f:
            json.dump(result.to_json(), f)
            f.write("\n")
        return is_success(result)

    results = util.parallel_runner(run_it, [(t.id, t) for t in config.tasks], succeeded=succeeded, jobs=config.jobs)

    total = len(results)
    success = len([x for x in results if is_success(x)])

    print(f"Finished {total} tasks: {success} Success, {total-success} Failures")

    # Post-run actions (e.g., upload results via environment-specific ingest)
    if config.deployment_env:
        config.deployment_env.post_run(tasks_result_file)

    return True


def agent_main(agent_builder: AgentBuilder, args: list[str] | None = None) -> bool:
    """
    A simple entry point for an agent to be run as a stand-alone file.

    Clients that use this function should provide an entry point to their agent like:

        def agent_builder(args: list[str]=[], prompt:str|None=None) -> Agent:
            return MyAgent()

        if __name__ == '__main__':
            agent_main(agent_builder)
    """
    if args is None:
        args = sys.argv[1:]
    try:
        idx = args.index("--")
        agent_args: list[str] = args[idx + 1 :]
        args = args[:idx]
    except ValueError:
        agent_args = []

    arguments: Namespace = mk_parser(
        parent=None, with_agent=agent_builder is None
    ).parse_args(args)
    config: RunConfiguration = parse_arguments(arguments, agent_builder=agent_builder)
    if agent_args:
        config.agent_builder.add_args(agent_args)
    return run_config(config)


def run_ns(args: Namespace, extra_args: list[str] | None = None) -> bool:
    """Assumes that agent is set"""
    config = parse_arguments(args, None)
    if extra_args:
        config.agent_builder.add_args(extra_args)
    return run_config(config)


def auto_main() -> bool:
    return agent_main(AgentBuilder.of_agent(AutoAgent))


def tactic_main() -> bool:
    return agent_main(OneShotBuilder())

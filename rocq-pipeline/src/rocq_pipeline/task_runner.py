import json
import os
import traceback
import uuid
from argparse import ArgumentParser, Namespace
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from dotenv import load_dotenv
from observability import (
    ObservabilityConfig,
    add_log_context,
    get_logger,
    setup_observability,
    trace_context,
)
from opentelemetry.trace import Link, SpanContext, Status, StatusCode
from rocq_doc_manager import rc_sess
from rocq_dune_util import DuneError, rocq_args_for

import rocq_pipeline.tasks as Tasks
from rocq_pipeline import loader, util
from rocq_pipeline.agent import (
    AgentBuilder,
    AutoAgent,
    OneShotBuilder,
    TaskResult,
)
from rocq_pipeline.agent.proof.trace_cursor import TracingCursor
from rocq_pipeline.args import load_tasks
from rocq_pipeline.args_util import split_args
from rocq_pipeline.env_manager import Environment, EnvironmentRegistry
from rocq_pipeline.schema import task_output
from rocq_pipeline.task_modifiers import task_mod
from rocq_pipeline.with_deps import rocq_deps_for

logger = get_logger("task_runner")

load_dotenv()


def init_logging(env: Environment) -> None:
    """Initialise logging based on the current environment and CLI flags.

    This is intentionally called from entrypoints *after* argument parsing
    so that ``--env`` can influence the OTLP endpoint.
    """
    otlp_endpoint = env.get_otlp_endpoint()
    observability_config = ObservabilityConfig(
        service_name="rocq_agent",
        log_level=os.getenv("LOG_LEVEL", "INFO"),
        otlp_endpoint=env.get_otlp_endpoint(),
        enable_console_logging=os.getenv("ENABLE_CONSOLE_LOGGING", "false").lower()
        == "true",
    )
    setup_observability(observability_config)
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
    # We will parse these afterwards since other command line parameters
    # might (in the future) set up additional TaskModifiers
    parser.add_argument(
        "--task-mod",
        action="append",
        default=[],
        help="Additional task modifiers to add to all tasks. Can be passed multiple times.",
    )

    # Add deployment mode flag
    parser.add_argument(
        "--env",
        type=str,
        default="none",
        help="Deployment environment (e.g., 'local', 'staging', 'ci'). Default: none",
    )

    return parser


# def main(agent_type: type[Agent], args: list[str] | None = None) -> bool:
#     pass


def collect_env_tags(prefix: str = "TAG_") -> task_output.Tags:
    """
    Collect environment variables that represent tags.

    For each variable of the form TAG_FOO=bar, this returns an entry
    {"foo": "bar"} in the resulting dict.
    """
    tags: dict[str, str] = {}
    for key, value in os.environ.items():
        if key.startswith(prefix):
            tag_key = key[len(prefix) :].lower()
            tags[tag_key] = value
    return task_output.Tags(tags)


async def run_task(
    build_agent: AgentBuilder,
    project: Tasks.Project,
    task: Tasks.Task,
    run_id: str,
    tags: task_output.Tags,
    progress: util.ProgressCallback,
    parent_span_context: SpanContext | None = None,
) -> task_output.TaskOutput | None:
    """
    Build an agent using [build_agent] and invoke it on the task.

    Creates an independent trace for this task with a link to the parent
    run_config trace if parent_span_context is provided.
    """
    # Add run_id to log context for this thread
    add_log_context("run_id", run_id)

    task_id: str = task.get_id()
    add_log_context("task_id", task_id)

    timestamp_iso_8601 = datetime.now(UTC).isoformat()

    # Create a new independent trace with a link to the parent span
    trace_id: str | None = None
    links = []
    if parent_span_context and parent_span_context.is_valid:
        links.append(Link(parent_span_context))

    # Prepare tracer_kwargs for creating a root span (new trace) with links
    tracer_kwargs: dict[str, Any] = {"context": None}  # No parent context = new trace
    if links:
        tracer_kwargs["links"] = links

    with trace_context(
        "run_task",
        tracer_kwargs=tracer_kwargs,
        attributes={
            "task.id": task_id,
            "run.id": run_id,
        },
    ) as span:
        # Get trace_id from this new span
        span_context = span.get_span_context()
        if span_context.is_valid:
            trace_id = format(span_context.trace_id, "032x")
        else:
            logger.warning(f"Invalid SpanContext for task {task_id} from run {run_id}")

        task_result: TaskResult | None = None
        agent = build_agent(task.prompt)

        agent_class_checksum = agent.cls_checksum()
        agent_instance_checksum = agent.checksum()
        agent_class_provenance = agent.cls_provenance_json()
        agent_instance_provenance = agent.provenance_json()
        # Simply printing the Provenance data make them separate key value pairs in the log.
        # To keep them together so they are easy to retrieve, we wrap them in a "json".
        #
        # TODO: avoid re-logging if we've already logged AgentClassProvenance
        # or AgentProvenance with this checksum.
        logger.info(
            "AgentClassProvenance",
            cls_checksum=agent_class_checksum,
            cls_name=agent.cls_name(),
            cls_provenance={"cls_provenance": agent_class_provenance},
        )
        logger.info(
            "AgentProvenance",
            cls_checksum=agent_class_checksum,  # For correlation with class
            checksum=agent_instance_checksum,
            name=agent.name(),
            provenance={"provenance": agent_instance_provenance},
        )

        try:
            task_file = project.path / task.file
            progress.status(0.01, "🔃")

            task_mod_plugins = rocq_deps_for(task.modifiers)
            # We shouldn't need plugins on both `Agent` and `AgentBuilder`,
            # but it really depends how flexible the plugin system is.
            # `Agent` must be completely portable across environments, so
            # if any amount of plugin logic is environment-dependent, then
            # we need to put that logic in the `AgentBuilder`.
            agent_plugins = rocq_deps_for([build_agent, agent])
            plugins = task_mod_plugins + agent_plugins

            try:
                rocq_args = rocq_args_for(
                    task_file,
                    cwd=project.path,
                    plugins=plugins,
                )
            except DuneError as e:
                logger.error(
                    f"Could not get arguments for file {task_file}, using no arguments.\n{e.stderr}"
                )
                rocq_args = []

            async with rc_sess(
                task_file,
                rocq_args=rocq_args,
                cwd=str(project.path),
                load_file=True,
            ) as rc:
                progress.status(0.05, "🔃")
                if not await task.locator.go_to(rc):
                    msg = f"{task_id}: locator returned false"
                    progress.log(msg)
                    span.set_status(Status(StatusCode.ERROR, msg))
                    raise ValueError("Locator failed to find position in file")
                progress.status(0.1, "🔃")
                for mod in task.modifiers:
                    await mod.run(rc)
                progress.status(0.15, "💭")
                task_result = await agent.run(TracingCursor.of_cursor(rc))
        except Exception as e:
            progress.log(f"Failure with {e}:\n{traceback.format_exc()}")
            task_result = TaskResult.from_exception(e)
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR, str(e)))
        finally:
            progress.status(0.95, "🔚")

        assert task_result is not None

        # Log the result
        if not task_result.success:
            if not task_result.exception:
                span.set_status(Status(StatusCode.ERROR, task_result.message))
                progress.log(
                    f"{agent.name()} gave up with message: {task_result.message}"
                )
                logger.info(
                    "TaskStatus",
                    task_status=task_result.success,
                    task_result_message=task_result.message,
                )
            else:
                # Note: except block above will handle printing a rich stack trace and
                # invoking `span.set_status` if an `ExecutionError` was raised.
                pass
        else:
            span.set_status(Status(StatusCode.OK))
            progress.log(f"task completed: {task_result.message}")
            logger.info(
                "TaskStatus",
                task_status=task_result.success,
                task_result_message=task_result.message,
            )

        dataset_id = (project.name or "").strip()
        if not dataset_id:
            raise ValueError(
                "Missing project name in task file; cannot derive dataset_id."
            )

        task_tags = task_output.Tags(dict(tags.value))
        for task_tag in task.tags:
            task_tags.value.update({f"TASK_{task_tag}": task_tag})

        return task_result.to_task_output(
            run_id=run_id,
            task_kind=task.get_kind(),
            task_id=task_id,
            dataset_id=dataset_id,
            timestamp_utc=timestamp_iso_8601,
            agent_cls_checksum=agent_class_checksum,
            agent_checksum=agent_instance_checksum,
            trace_id=trace_id,
            metadata=task_output.Metadata(tags=task_tags),
        )


def load_agent(agent_desc: str) -> AgentBuilder:
    try:
        agent_builder = loader.load_from_str(agent_desc, "dyn_loaded_agent")
        if isinstance(agent_builder, AgentBuilder):
            return agent_builder
        raise Exception(f"{agent_builder} is not an [AgentBuilder].")
    except Exception as err:
        raise ValueError(f"Failed to load AgentBuilder from {agent_desc}.") from err


@dataclass
class RunConfiguration:
    agent_builder: AgentBuilder
    tasks: list[tuple[Tasks.Project, Tasks.Task]]
    tasks_name: str
    output_dir: Path
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

    (tasks_name, tasks) = load_tasks(arguments)

    if arguments.task_mod:
        task_mods = [task_mod.of_string(m) for m in arguments.task_mod]
        for _, task in tasks:
            if task.modifiers:
                task.modifiers.extend(task_mods)
            else:
                task.modifiers = task_mods

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

    # Create a dispatcher span for setup and enqueuing
    parent_span_context: SpanContext | None = None

    now_str = datetime.now().strftime("%Y%m%d_%H%M")
    tasks_result_file: Path = (
        config.output_dir / f"{config.tasks_name}_results_{now_str}.jsonl"
    )
    run_id: str = str(uuid.uuid4())

    with trace_context(
        "run_config/begin",
        attributes={
            "run.id": run_id,
            "tasks.count": len(config.tasks),
            "jobs": config.jobs,
        },
    ) as dispatcher_span:
        # Capture parent span context before closing dispatcher span
        span_context = dispatcher_span.get_span_context()
        if span_context.is_valid:
            parent_span_context = span_context

        logger.info(f"Run {len(config.tasks)} tasks with {config.jobs} workers")
        dispatcher_span.add_event(
            "run_tasks",
            {
                "task_count": len(config.tasks),
                "worker_count": config.jobs,
            },
        )

    # Dispatcher span is now closed - workers will run independently

    async def run_it(
        proj_task: tuple[Tasks.Project, Tasks.Task], progress: util.ProgressCallback
    ) -> task_output.TaskOutput | None:
        proj, task = proj_task
        return await run_task(
            config.agent_builder,
            proj,
            task,
            run_id,
            tags=config.tags,
            progress=progress,
            parent_span_context=parent_span_context,
        )

    # Touch the file early to make sure that it is createable
    Path(tasks_result_file).touch()

    def is_success(result: task_output.TaskOutput | BaseException | None) -> bool:
        if result is None or isinstance(result, BaseException):
            return False
        return str(result.status.value.kind) == "Success"

    def succeeded(result: task_output.TaskOutput | None) -> bool:
        if result is None:
            return False
        with open(tasks_result_file, "a", encoding="utf8") as f:
            json.dump(result.to_json(), f)
            f.write("\n")
        return is_success(result)

    results: list[task_output.TaskOutput | BaseException | None] = util.parallel_runner(
        run_it,
        [(f"{t[0].get_id()}#{t[1].get_id()}", t) for t in config.tasks],
        succeeded=succeeded,
        jobs=config.jobs,
    )

    total = len(results)
    success = len([x for x in results if is_success(x)])

    print(f"Finished {total} tasks: {success} Success, {total - success} Failures")

    # Post-run actions (e.g., upload results via environment-specific ingest)
    if config.deployment_env:
        config.deployment_env.post_run(tasks_result_file)

    return True


def agent_main(agent_builder: AgentBuilder, args: list[str] | None = None) -> bool:
    """
    A simple entry point for an agent to be run as a stand-alone file.

    Clients that use this function should provide an entry point to their agent like:

    ```
    if __name__ == '__main__':
        agent_main(AgentBuilder.of_agent(MyAgent))
    ```
    """
    args, agent_args = split_args(args)

    arguments: Namespace = mk_parser(
        parent=None, with_agent=agent_builder is None
    ).parse_args(args)
    try:
        config: RunConfiguration = parse_arguments(
            arguments, agent_builder=agent_builder
        )
    except ValueError as err:
        print(f"Failed setting up the run: {err}")
        return False
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

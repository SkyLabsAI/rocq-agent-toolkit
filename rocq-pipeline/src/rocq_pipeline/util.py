import asyncio
from collections.abc import Awaitable, Callable
from concurrent.futures import CancelledError, Future, ThreadPoolExecutor, as_completed
from itertools import count
from types import TracebackType
from typing import cast
from warnings import deprecated

from observability import get_logger
from rich.progress import (
    BarColumn,
    Progress,
    TaskID,
    TaskProgressColumn,
    TextColumn,
)

logger = get_logger(__name__)


class MockProgress:
    def __init__(self) -> None:
        self._ids = count(0)

    def add_task(self, name: str, **kwargs: object) -> TaskID:
        _ = (name, kwargs)
        return cast(TaskID, next(self._ids))

    def remove_task(self, name: TaskID, **kwargs: object) -> None:
        _ = (name, kwargs)

    def update(self, which: TaskID, **kwargs: object) -> None:
        _ = (which, kwargs)

    def __enter__(self) -> "MockProgress":
        return self

    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc: BaseException | None,
        tb: TracebackType | None,
    ) -> None:
        _ = (exc_type, exc, tb)


class Feedback:
    def __init__(
        self,
        show_name: str,
        progress: Progress | None = None,
        current_task_id: TaskID | None = None,
        max: float = 100,
    ) -> None:
        self._progress = progress
        self._current_task_id = current_task_id
        self._max = max
        self._show_name = show_name

    def status(self, percent: float | None = None, status: str | None = None) -> None:
        if self._progress and self._current_task_id:
            self._progress.update(
                self._current_task_id,
                completed=None if percent is None else percent * self._max,
                description=None
                if status is None
                else f"[yellow]-> {self._show_name} {status}",
            )

    @deprecated("use [status] instead")
    def __call__(self, percent: float | None = None, status: str | None = None) -> None:
        return self.status(percent, status)

    def log(self, message: str) -> None:
        if self._progress:
            self._progress.console.print(f"{self._show_name}: {message}")
        else:
            print(f"{self._show_name}: {message}")


type ProgressCallback = Feedback


def parallel_runner[T, U](
    run: Callable[[T, ProgressCallback], Awaitable[U]],
    tasks: list[tuple[str, T]],
    succeeded: Callable[[U], bool] | None = None,
    jobs: int = 1,
    progress: bool = True,
) -> list[U | BaseException]:
    total_tasks = len(tasks)
    with (
        Progress(
            TextColumn("[bold blue]{task.description}"),
            BarColumn(bar_width=None),  # Auto-width bar
            TaskProgressColumn(),
            transient=True,  # Bars disappear after completion
        )
        if progress
        else MockProgress()
    ) as pb:
        overall = pb.add_task("[green]Overall Progress", total=total_tasks, completed=0)

        async def _await(aw: Awaitable[U]) -> U:
            return await aw

        def go(name_val: tuple[str, T]) -> tuple[str, U]:
            [name, val] = name_val
            MAX_NAME_LEN = 35
            PROGRESS_MAX = 100
            show_name: str = (
                (".." + name[-MAX_NAME_LEN + 2 :]) if len(name) > MAX_NAME_LEN else name
            )

            current_task_id = pb.add_task(
                f"[yellow]-> {show_name}  ", total=PROGRESS_MAX, completed=0
            )
            if isinstance(pb, Progress):
                feedback = Feedback(show_name, pb, current_task_id, PROGRESS_MAX)
            else:
                feedback = Feedback(show_name)
            result = asyncio.run(_await(run(val, feedback)))
            pb.update(
                current_task_id,
                completed=PROGRESS_MAX,
                description=f"[yellow]-> {show_name}",
            )
            pb.remove_task(current_task_id)

            return (name, result)

        success: int = 0
        failure: int = 0
        final_results: dict[int, U | BaseException] = {}

        with ThreadPoolExecutor(max_workers=jobs) as tpe:
            # Submit all tasks and keep track of the future objects, but
            # elide the mapping from `Future` to `T` since we don't use it.
            #
            # We want to return a list matching the order of `tasks` so we use
            # `futures_order` to maintain a mapping from `Future` to task-idx
            futures_order: dict[Future, int] = {}
            for i, task in enumerate(tasks):
                future = tpe.submit(go, task)
                futures_order[future] = i

            # as_completed yields futures the moment they finish
            for future in as_completed(futures_order.keys()):
                future_cancelled_or_exception: bool = False
                final_result: U | BaseException
                try:
                    if future.cancelled():
                        future_cancelled_or_exception = True
                        final_result = CancelledError()
                    elif (final_exception := future.exception()) is not None:
                        future_cancelled_or_exception = True
                        final_result = final_exception
                    else:
                        _, final_result = future.result()
                except CancelledError as e_cancelled:
                    future_cancelled_or_exception = True
                    final_result = e_cancelled
                except Exception as e_unexpected:
                    future_cancelled_or_exception = True
                    final_result = e_unexpected
                    logger.error(
                        "Unexpected error during task processing", exc_info=e_unexpected
                    )

                final_results[futures_order[future]] = final_result

                # Note: while `U` might derive from `BaseException`, `final_result` is guaranteed to have
                # type `U` iff `future_cancelled_or_exception=False`
                if succeeded is None or (
                    not future_cancelled_or_exception
                    and succeeded(cast(U, final_result))
                ):
                    success += 1
                else:
                    failure += 1

                if succeeded is None:
                    desc = f"{success} / {total_tasks}"
                else:
                    desc = f"[green]{success}[/green] & [red]{failure}[/red] / {total_tasks}"
                pb.update(overall, advance=1, description=desc)

        return [final_result for _, final_result in sorted(final_results.items())]


def main() -> None:
    import time
    from random import random

    async def delay(x: int, _: ProgressCallback) -> bool:
        time.sleep(random())
        return 0.5 < random()

    def succeeded(x: bool) -> bool:
        return x

    parallel_runner(
        delay, [(str(x), x) for x in range(0, 20)], succeeded=succeeded, jobs=3
    )

from collections.abc import Callable
from concurrent.futures.thread import ThreadPoolExecutor
from typing import Any

from rich.progress import (
    BarColumn,
    Progress,
    TaskProgressColumn,
    TextColumn,
)


class MockProgress:
    def add_task(self, name:str, **kwargs) -> Any: # type: ignore
        return None
    def update(self, which:Any, **kwargs) -> Any: # type: ignore
        return None
    def __enter__(self) -> "MockProgress":
        return self
    def __exit__(self, a:Any, b:Any, c:Any) -> Any:
        pass

def parallel_runner[T, U](run: Callable[[T, Callable[[(float|None),(str|None)],None]], U], tasks: list[tuple[str, T]], succeeded:Callable[[U],bool]|None =None, jobs:int=1, progress:bool=True) -> list[U]:
    total_tasks = len(tasks)

    with (Progress(
        TextColumn("[bold blue]{task.description}"),
        BarColumn(bar_width=None), # Auto-width bar
        TaskProgressColumn(),
        transient=True, # Bars disappear after completion
    ) if progress else MockProgress()) as pb:
        overall = pb.add_task(
                    "[green]Overall Progress",
                    total=total_tasks,
                    completed=0
                )

        def go(name_val: tuple[str, T]) -> tuple[str, U]:
            [name, val] = name_val
            MAX_NAME_LEN = 35
            PROGRESS_MAX = 100
            show_name:str = (".." + name[-MAX_NAME_LEN+2:]) if len(name) > MAX_NAME_LEN else name

            current_task_id = pb.add_task(
                            f"[yellow]-> {show_name}",
                            total=PROGRESS_MAX,
                            completed=0
                        )
            def update(value: float|None=None, status: str|None=None) -> None:
                pb.update(current_task_id, completed=None if value is None else value*PROGRESS_MAX, description=status)

            result = run(val, update)
            pb.update(
                current_task_id,
                completed=PROGRESS_MAX,
                description=f"[yellow]-> {show_name}"
            )

            return (name, result)

        success:int = 0
        failure:int = 0
        final_result: list[U] = []

        with ThreadPoolExecutor(max_workers=jobs) as tpe:
            for (_, result) in tpe.map(go, tasks):
                final_result.append(result)
                if succeeded is None or succeeded(result):
                    success = success + 1
                else:
                    failure = failure + 1
                if succeeded is None:
                    pb.update(overall,
                        advance=1,
                        description=f"{success} / {total_tasks}")
                else:
                    pb.update(overall,
                        advance=1,
                        description=f"[green]{success}[/green] & [red]{failure}[/red] / {total_tasks}")
        return final_result

def main() -> None:
    import time
    from random import random
    def delay(x: int, _:Any) -> bool:
        time.sleep(random())
        return 0.5 < random()
    def succeeded(x:bool) -> bool:
        return x
    parallel_runner(delay, [(str(x),x) for x in range(0, 20)], succeeded=succeeded,jobs=3)

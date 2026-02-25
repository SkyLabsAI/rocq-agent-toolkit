from collections.abc import Callable, Iterator
from contextlib import contextmanager
from time import sleep
from typing import Literal

from rich.console import Group
from rich.live import Live
from rich.panel import Panel


def generate_content(step):
    """Creates the content to be placed inside the box."""
    return f"Processing item [bold cyan]#{step}[/bold cyan]...\nProgress: {step * 10}%"


@contextmanager
def build_ui(
    kind: Literal["quiet", "tui", "status"],
) -> Iterator[Callable[[str, str | None], None]]:
    if kind == "quiet":
        yield lambda _msg, _script: None
    elif kind == "status":
        last = None

        def status_update(msg: str, script: str | None = None) -> None:
            if msg != last:
                print(msg)

        yield status_update
    elif kind == "tui":
        with Live(Panel(generate_content(0)), refresh_per_second=4) as live:

            def tui_update(message: str, script: str | None) -> None:
                # We recreate the Group to keep the message on top and the box below
                if script:
                    new_content = Group(
                        message,
                        Panel(script, title="Proof script", border_style="bright_blue"),
                    )
                else:
                    new_content = Group(message)

                live.update(new_content)
                sleep(0.1)

            yield tui_update
    else:
        raise AssertionError(
            "Invalid `kind` value to `build_ui`. Must be one of 'quiet', 'tui', or 'status'"
        )

from collections.abc import Iterator
from contextlib import contextmanager
from typing import Literal, Protocol

from rich.console import Group
from rich.live import Live
from rich.panel import Panel


class Controller(Protocol):
    def print(self, msg: str) -> None: ...
    def proof_visible(self, visible: bool) -> None: ...
    def set_proof_script(self, script: str) -> None: ...
    def set_active(self, tac: str) -> None: ...
    def update(self) -> None: ...


class QuietController(Controller):
    def __init__(self, quiet: bool) -> None:
        self._quiet = quiet

    def print(self, msg: str) -> None:
        if not self._quiet:
            print(msg)

    def proof_visible(self, visible: bool) -> None:
        pass

    def set_proof_script(self, script: str) -> None:
        pass

    def set_active(self, tac: str) -> None:
        pass

    def update(self) -> None:
        pass


class TUIController(Controller):
    def __init__(self, live: Live) -> None:
        self._visible = False
        self._proof_script = ""
        self._active = ""
        self._live = live

    def print(self, msg: str) -> None:
        print(msg)

    def proof_visible(self, visible: bool) -> None:
        self._visible = visible
        if not self._visible:
            self._proof_script = ""
            self._active = ""
        self.update()

    def set_proof_script(self, script: str) -> None:
        self._proof_script = script
        self.update()

    def set_active(self, tac: str) -> None:
        self._active = tac
        self.update()

    def update(self) -> None:
        if not self._visible:
            content = Group()
        else:
            entries = []
            if self._proof_script:
                entries.append(
                    Panel(
                        self._proof_script,
                        title="Proof script",
                        border_style="bright_blue",
                    )
                )
            if self._active:
                entries.append(
                    Panel(self._active, title="Running...", border_style="bright_blue")
                )
            content = Group(*entries)

        self._live.update(content)


@contextmanager
def build_ui(
    kind: Literal["quiet", "tui", "status"],
) -> Iterator[Controller]:
    if kind == "quiet":
        yield QuietController(quiet=True)
    elif kind == "status":
        yield QuietController(quiet=False)
    elif kind == "tui":
        with Live(Group(), refresh_per_second=40) as live:
            yield TUIController(live)
    else:
        raise AssertionError(
            "Invalid `kind` value to `build_ui`. Must be one of 'quiet', 'tui', or 'status'"
        )

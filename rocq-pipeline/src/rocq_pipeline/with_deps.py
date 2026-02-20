from typing import Any, Protocol, override, runtime_checkable

from rocq_dune_util import DuneRocqPlugin


@runtime_checkable
class UsingRocqDependencies(Protocol):
    def rocq_deps(self) -> list[DuneRocqPlugin]:
        """Return the extra dependencies required by the object."""
        ...


def rocq_deps_for(what: Any) -> list[DuneRocqPlugin]:
    """Compute the Rocq dependencies of `what`.
    If `what` is a list, it will compute the dependencies of all list items."""
    if isinstance(what, list):
        return [dep for elem in what for dep in rocq_deps_for(elem)]
    if isinstance(what, UsingRocqDependencies):
        return what.rocq_deps()
    return []


class NoRocqDependencies(UsingRocqDependencies):
    """A default way to implement `UsingRocqDependencies` when a class does not
    need additional Rocq Dependencies."""

    @override
    def rocq_deps(self) -> list[DuneRocqPlugin]:
        return []

"""Python API for the Rocq document manager.

This package provides a Python interface to interact with the Rocq document
manager.
"""

from .plugin_registry import DepType, PluginRegistry, PluginRegistration
from .rocq_cursor import RocqCursor
from .rocq_doc_manager import RocqDocManager


def create(
    rocq_args: list[str],
    file_path: str,
    chdir: str | None = None,
    dune: bool = False,
    dune_disable_global_lock: bool = True,
    *,
    auto_discover_plugins: bool = True,
    plugin_names: list[str] | None = None,
) -> RocqDocManager:
    return RocqDocManager(
        rocq_args,
        file_path,
        chdir,
        dune,
        dune_disable_global_lock,
        auto_discover_plugins=auto_discover_plugins,
        plugin_names=plugin_names,
    )


__all__ = [
    "create",
    "RocqDocManager",
    "RocqCursor",
    "PluginRegistry",
    "PluginRegistration",
    "DepType",
]

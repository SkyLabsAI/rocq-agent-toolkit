"""Python bindings for rocq-term-deps plugin.

This module provides query-only access to the DepsOf and DepsOfJSON
vernacular commands from the rocq-term-deps plugin.
"""

from __future__ import annotations

import json
import logging
from pathlib import Path
from typing import Any

from rocq_doc_manager import RocqCursor
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_doc_manager.plugin_registry import DepType, PluginRegistry

logger = logging.getLogger(__name__)

__all__ = ["deps_of", "deps_of_json"]


def deps_of(cursor: RocqCursor, ident: str) -> str | rdm_api.Err[None]:
    """Get the dependencies of a constant using DepsOf.

    Args:
        cursor: A RocqCursor instance.
        ident: The name of the constant to query (e.g., "Nat.add").

    Returns:
        The text output from DepsOf, or the Err.
    """
    # Use rollback context to ensure plugin import doesn't persist
    with cursor.ctx():
        # Require the plugin first
        deps_of_plugin_logpath = "skylabs_ai.tools.term_deps.plugin"
        req_import_reply = cursor.RequireImport(logpath=deps_of_plugin_logpath)
        if isinstance(req_import_reply, rdm_api.Err):
            return req_import_reply

        return cursor.query_text(f"DepsOf {ident}.", index=0)


def deps_of_json(cursor: RocqCursor, ident: str) -> dict[str, Any] | rdm_api.Err[None]:
    """Get the dependencies of a constant using DepsOfJSON.

    Args:
        cursor: A RocqCursor instance.
        ident: The name of the constant to query (e.g., "Nat.add").

    Returns:
        A dictionary with keys:
        - "name": The constant name
        - "kind": One of "Def", "Undef", "OpaqueDef", "Primitive", "Symbol"
        - "inductive_deps": List of inductive type names
        - "constant_deps": List of constant names
        or the Err.
    """
    # Use rollback context to ensure plugin import doesn't persist
    with cursor.ctx():
        # Require the plugin first
        deps_of_json_plugin_logpath = "skylabs_ai.tools.term_deps.plugin"
        req_import_reply = cursor.RequireImport(logpath=deps_of_json_plugin_logpath)
        if isinstance(req_import_reply, rdm_api.Err):
            return req_import_reply

        # Query for the dependencies
        deps_reply = cursor.query_json(f"DepsOfJSON  ident}.", index=0)
        if isinstance(deps_reply, rdm_api.Err):
            return deps_reply

    # Validate the structure matches expected format
    assert isinstance(deps_reply, dict)
    for k_str in {"name", "kind"}:
        assert k_str in deps_reply
        assert isinstance(deps_reply[k_str], str)
    for k_str_list in {"inductive_deps", "constant_deps"}:
        assert k_str_list in deps_reply
        assert isinstance(deps_reply[k_str_list], list)
        for v in deps_reply[k_str_list]:
            assert isinstance(v, str)

    return deps_reply


def _register_plugin() -> None:
    """Register this plugin with the rocq-doc-manager plugin registry.
    
    This function is called via the entry point system when the plugin
    is discovered by rocq-doc-manager.
    """
    # Find the plugin.v file relative to this package
    # The plugin.v file is at rocq-term-deps/theories/plugin.v
    # We need to find it relative to the Python package location
    package_file = __file__
    package_dir = Path(package_file).parent.parent.parent.parent
    plugin_v = package_dir / "theories" / "plugin.v"

    if plugin_v.exists():
        PluginRegistry.register(
            opam_package_name="rocq-term-deps",
            v_files=[plugin_v],
            dep_type=DepType.WORKSPACE_DEPS,
        )
    else:
        logger.warning(
            f"Could not find plugin.v file at {plugin_v}. "
            "Plugin registration may not work correctly."
        )


# Register the plugin when the module is imported (for backward compatibility)
# The entry point will also call this function
_register_plugin()

"""Registry for python bindings of Rocq plugins.

This module provides a registry system for Python bindings of Rocq plugins.
Plugins can register themselves to automatically add their `.v` files as either
`extra_deps` or `workspace_deps` when used with RocqDocManager.

Plugins are automatically made available to RocqDocManager instances that are
created with the `auto_discover_plugins` flag set to True.
"""

from __future__ import annotations

import importlib.metadata
import logging
from collections.abc import Callable
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Any

from rocq_dune_util import dune_sourceroot, rocq_args_for

logger = logging.getLogger(__name__)


class DepType(Enum):
    """Type of dependency for plugin files."""

    EXTRA_DEPS = "extra_deps"
    WORKSPACE_DEPS = "workspace_deps"


@dataclass(frozen=True)
class PluginRegistration:
    """Registration information for a Rocq plugin."""

    opam_package_name: str
    """The opam package name (e.g., 'rocq-term-deps')."""

    v_files: list[Path]
    """List of `.v` files provided by this plugin."""

    dep_type: DepType
    """Whether files should be added as extra_deps or workspace_deps."""

    def get_extra_deps(self) -> list[Path]:
        """Get extra_deps if this plugin uses EXTRA_DEPS."""
        if self.dep_type == DepType.EXTRA_DEPS:
            return self.v_files
        return []

    def get_workspace_deps(self) -> list[Path]:
        """Get workspace_deps if this plugin uses WORKSPACE_DEPS."""
        if self.dep_type == DepType.WORKSPACE_DEPS:
            return self.v_files
        return []


class PluginRegistry:
    """Registry for Python bindings of Rocq plugins."""

    _registry: dict[str, PluginRegistration] = {}
    _discovered_modules: set[str] = set()
    _entry_point_group = "rocq_doc_manager.plugins"

    @classmethod
    def register(
        cls,
        opam_package_name: str,
        v_files: list[str | Path],
        *,
        dep_type: DepType = DepType.EXTRA_DEPS,
    ) -> None:
        """Register a plugin with the registry.

        Args:
            opam_package_name: The opam package name.
            v_files: List of `.v` files provided by this plugin.
            dep_type: Whether files should be added as extra_deps or workspace_deps.
        """
        v_paths = [Path(f) for f in v_files]
        registration = PluginRegistration(
            opam_package_name=opam_package_name,
            v_files=v_paths,
            dep_type=dep_type,
        )
        cls._registry[opam_package_name] = registration

    @classmethod
    def discover_plugins(cls) -> None:
        """Discover and register plugins via entry points.
        
        This method caches which entry point modules have been invoked,
        and skips re-invoking them on subsequent calls.
        """
        try:
            eps = importlib.metadata.entry_points(group=cls._entry_point_group)
            for ep in eps:
                # Skip if this module has already been discovered
                if ep.name in cls._discovered_modules:
                    logger.debug(
                        f"Skipping already-discovered plugin entry point: {ep.name}"
                    )
                    continue
                
                try:
                    register_func: Callable[[], None] = ep.load()
                    register_func()
                    # Mark this module as discovered
                    cls._discovered_modules.add(ep.name)
                except Exception as e:
                    logger.warning(
                        f"Failed to load plugin entry point {ep.name}: {e}",
                        exc_info=True,
                    )
        except Exception as e:
            logger.warning(f"Failed to discover plugins: {e}", exc_info=True)

    @classmethod
    def get_registration(cls, opam_package_name: str) -> PluginRegistration | None:
        """Get registration for a plugin by opam package name.
        
        Only discovers plugins if the requested package hasn't been registered yet.
        """
        # Only discover plugins if this package isn't already registered
        if opam_package_name not in cls._registry:
            cls.discover_plugins()
        return cls._registry.get(opam_package_name)

    @classmethod
    def get_all_registrations(cls, *, skip_discovery: bool = False) -> dict[str, PluginRegistration]:
        """Get all registered plugins.
        
        Args:
            skip_discovery: If True, skip plugin discovery and only return
                          already-registered plugins. Defaults to False.
        
        Returns:
            A dictionary mapping opam package names to their registrations.
        """
        if not skip_discovery:
            cls.discover_plugins()
        return cls._registry.copy()

    @classmethod
    def get_import_logpath(cls, opam_package_name: str) -> str | None:
        """Get the import logpath for a plugin.

        The logpath is typically the opam package name, but this can be
        overridden by plugins if needed.

        Args:
            opam_package_name: The opam package name.

        Returns:
            The import logpath, or None if the plugin is not registered.
        """
        registration = cls.get_registration(opam_package_name)
        if registration is None:
            return None
        # For now, use the opam package name as the logpath
        # Plugins can override this behavior if needed
        return registration.opam_package_name

    @classmethod
    def get_rocq_args(
        cls,
        opam_package_name: str,
        *,
        file: str | Path,
        cwd: str | Path | None = None,
        build: bool = False,
    ) -> list[str] | None:
        """Get rocq-args for a plugin.

        This returns the rocq command-line arguments needed to use the plugin
        with the given file.

        Args:
            opam_package_name: The opam package name.
            file: The Rocq source file to get args for.
            cwd: Alternative current working directory.
            build: Whether to build dependencies.

        Returns:
            The rocq-args, or None if the plugin is not registered.
        """
        registration = cls.get_registration(opam_package_name)
        if registration is None:
            return None

        extra_deps = registration.get_extra_deps()
        workspace_deps = registration.get_workspace_deps()

        return rocq_args_for(
            file,
            cwd=cwd,
            build=build,
            extra_deps=extra_deps if extra_deps else None,
            workspace_deps=[str(d) for d in workspace_deps] if workspace_deps else None,
        )

    @classmethod
    def collect_plugin_deps(
        cls,
        *,
        plugin_names: list[str] | None = None,
        skip_discovery: bool = False,
    ) -> tuple[list[Path], list[Path]]:
        """Collect extra_deps and workspace_deps from registered plugins.

        Args:
            plugin_names: Optional list of plugin names to include.
                         If None, includes all registered plugins.

        Returns:
            A tuple of (extra_deps, workspace_deps) lists.
        """
        if not skip_discovery:
            cls.discover_plugins()
        extra_deps: list[Path] = []
        workspace_deps: list[Path] = []

        registrations: list[PluginRegistration] = []
        if plugin_names:
            for name in plugin_names:
                registration = cls.get_registration(name)
                if registration is not None:
                    registrations.append(registration)
                else:
                    logger.warning(f"Plugin {name} not found")
        else:
            registrations = list(cls._registry.values())

        for registration in registrations:
            extra_deps.extend(registration.get_extra_deps())
            workspace_deps.extend(registration.get_workspace_deps())

        return (extra_deps, workspace_deps)

    @classmethod
    def _find_dune_project(cls, start_dir: Path) -> Path | None:
        """Find dune-project file by walking up from start_dir."""
        current = start_dir.resolve()
        while current != current.parent:
            dune_project = current / "dune-project"
            if dune_project.exists():
                return dune_project
            current = current.parent
        return None

    @classmethod
    def _parse_dune_project_name(cls, dune_project_file: Path) -> str | None:
        """Parse package name from dune-project file.

        Looks for either:
        - (name <package-name>)
        - (package (name <package-name>))
        """
        try:
            contents = dune_project_file.read_text()
            # Simple parsing - look for (name ...) patterns
            # This is a simplified parser that handles the common cases
            lines = contents.splitlines()
            in_package = False
            for line in lines:
                line = line.strip()
                # Check for (name ...) at top level
                if line.startswith("(name ") and not in_package:
                    # Extract name from (name package-name)
                    name_part = line[6:].rstrip(")")
                    return name_part.strip()
                # Check for (package ...) block
                if line.startswith("(package"):
                    in_package = True
                    continue
                # Check for (name ...) inside package block
                if in_package and line.startswith("(name "):
                    name_part = line[6:].rstrip(")")
                    return name_part.strip()
                # End of package block
                if in_package and line.startswith(")"):
                    in_package = False
        except Exception:
            pass
        return None

    @classmethod
    def _find_v_files(cls, package_dir: Path) -> list[Path]:
        """Find all .v files in package directory, excluding build artifacts."""
        exclude = {"_build", ".git", "_opam", ".venv", "__pycache__"}
        v_files: list[Path] = []
        for v_file in package_dir.rglob("*.v"):
            # Skip files in excluded directories
            if any(part in exclude for part in v_file.parts):
                continue
            v_files.append(v_file)
        return v_files

    @classmethod
    def auto_register(
        cls,
        package_dir: str | Path | None = None,
        *,
        dep_type: DepType | None = None,
        cwd: str | Path | None = None,
        v_files: list[str | Path] | None = None,
    ) -> None:
        """Automatically register a plugin by discovering opam package name and .v files.

        This method:
        1. Finds the dune-project file (walking up from package_dir or cwd)
        2. Parses the package name from dune-project
        3. Finds all .v files in the package directory (or uses provided v_files)
        4. Registers the plugin

        Args:
            package_dir: Directory containing the package. If None, uses cwd or
                        tries to find from dune-project location.
            dep_type: Whether to use EXTRA_DEPS or WORKSPACE_DEPS. If None,
                     automatically determines based on whether package is in
                     dune workspace.
            cwd: Alternative current working directory for dune operations.
            v_files: Optional list of .v files to include. If provided, only
                    these files will be registered (and warnings will be emitted
                    for any missing files). If None, all .v files in the package
                    directory will be included.

        Raises:
            ValueError: If dune-project file cannot be found or package name
                       cannot be determined.
        """
        # Find dune-project file
        if package_dir is None:
            if cwd is None:
                package_dir = Path.cwd()
            else:
                package_dir = Path(cwd)
        else:
            package_dir = Path(package_dir)

        dune_project = cls._find_dune_project(package_dir)
        if dune_project is None:
            raise ValueError(
                f"Could not find dune-project file starting from {package_dir}"
            )

        # Parse package name
        package_name = cls._parse_dune_project_name(dune_project)
        if package_name is None:
            raise ValueError(
                f"Could not parse package name from {dune_project}"
            )

        # Determine package directory (directory containing dune-project)
        actual_package_dir = dune_project.parent

        # Find all .v files
        v_files_found = cls._find_v_files(actual_package_dir)
        if not v_files_found:
            logger.warning(
                f"No .v files found in {actual_package_dir} for package {package_name}"
            )
            return

        # Filter to only include specified files if v_files is provided
        if v_files is not None:
            # Resolve provided file paths
            v_files_specified: set[Path] = set()
            for v_file in v_files:
                v_file_path = Path(v_file)
                # Resolve relative paths relative to package_dir
                if not v_file_path.is_absolute():
                    v_file_path = actual_package_dir / v_file_path
                v_files_specified.add(v_file_path.resolve())

            # Filter found files to only include specified ones
            v_files_final = [
                v_file for v_file in v_files_found if v_file.resolve() in v_files_specified
            ]

            # Warn about missing files
            for v_file_spec in v_files_specified:
                if not any(v_file.resolve() == v_file_spec for v_file in v_files_found):
                    logger.warning(
                        f"Specified .v file not found: {v_file_spec} "
                        f"(for package {package_name})"
                    )
        else:
            v_files_final = v_files_found

        # Determine dep_type if not provided
        workspace_root: Path | None = None
        if dep_type is None:
            try:
                workspace_root = dune_sourceroot(cwd=cwd)
                # Check if package_dir is within workspace
                try:
                    actual_package_dir.resolve().relative_to(workspace_root.resolve())
                    dep_type = DepType.WORKSPACE_DEPS
                except ValueError:
                    # Not in workspace, use extra_deps
                    dep_type = DepType.EXTRA_DEPS
            except Exception:
                # If we can't determine workspace, default to extra_deps
                dep_type = DepType.EXTRA_DEPS

        # For workspace_deps, convert absolute paths to relative paths from workspace root
        if dep_type == DepType.WORKSPACE_DEPS and workspace_root is not None:
            workspace_root_resolved = workspace_root.resolve()
            v_files_relative = []
            for v_file in v_files_final:
                try:
                    rel_path = v_file.resolve().relative_to(workspace_root_resolved)
                    v_files_relative.append(rel_path)
                except ValueError:
                    # File is not under workspace root, skip it
                    logger.warning(
                        f"Skipping {v_file} - not under workspace root {workspace_root}"
                    )
            v_files_final = v_files_relative

        # Register the plugin
        cls.register(
            opam_package_name=package_name,
            v_files=v_files_final,
            dep_type=dep_type,
        )
        logger.debug(
            f"Auto-registered plugin {package_name} with {len(v_files_final)} .v files "
            f"as {dep_type.value}"
        )

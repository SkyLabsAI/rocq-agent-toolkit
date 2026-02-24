import os
import shlex
import subprocess
from collections.abc import Iterator
from pathlib import Path
from typing import Literal


class DuneError(Exception):
    def __init__(self, message: str, *, stdout: str, stderr: str) -> None:
        super().__init__(message)
        self.stdout = stdout
        self.stderr = stderr


def _run_dune(args: list[str], cwd: str | Path | None) -> str:
    res = subprocess.run(
        ["dune"] + args,
        capture_output=True,
        cwd=str(cwd) if cwd is not None else None,
    )
    stdout = res.stdout.decode(encoding="utf-8")
    if res.returncode != 0:
        stderr = res.stderr.decode(encoding="utf-8")
        message = f'Dune command "{shlex.join(["dune"] + args)}" failed'
        raise DuneError(message, stdout=stdout, stderr=stderr)
    return stdout


def dune_sourceroot(*, cwd: str | Path | None = None) -> Path:
    """
    Locates the dune source root, also known as the workspace directory.

    @param cwd: alternative current working directory (optional)
    @returns: the absolute path to the dune workspace directory if found
    @raises DuneError: if the source root cannot be located
    """
    args = ["exec", "--no-build", "--", "env"]
    output = _run_dune(args, cwd=cwd)
    for line in output.splitlines():
        parts = line.split("=", 1)
        if len(parts) != 2:
            continue
        if parts[0] == "DUNE_SOURCEROOT":
            return Path(parts[1])
    raise AssertionError("Unreachable code: no DUNE_SOURCEROOT variable")


def _parse_target(target: str) -> tuple[Path, str] | Path:
    if isinstance(target, Path):
        return Path(target)
    if len(target) == 0:
        raise ValueError("Invalid target (empty)")
    if target[0] != "@":
        return Path(target)
    parts = target[1:].rsplit("/", 1)
    path = Path("." if len(parts) == 1 else parts[0])
    name = parts[-1]
    if len(name) == 0:
        raise ValueError("Invalid target (empty alias)")
    return (path, name)


def _build_target(target: tuple[Path, str] | Path) -> str:
    if isinstance(target, Path):
        return str(target)
    path, name = target
    return f"@{str(path)}/{name}"


def _canonical_rel_path(path: Path, cwd: str | Path | None) -> Path:
    rel_base = Path(".") if cwd is None else Path(cwd)
    rel_base = Path(os.path.normpath(rel_base.absolute()))
    return path.absolute().relative_to(rel_base, walk_up=True)


def _relative_target(
    target: tuple[Path, str] | Path, cwd: str | Path | None
) -> tuple[Path, str] | Path:
    if isinstance(target, Path):
        return _canonical_rel_path(target, cwd)
    path, name = target
    return (_canonical_rel_path(path, cwd), name)


def dune_build(targets: list[str], *, cwd: str | Path | None = None) -> None:
    """
    Builds the given targets using dune. The targets, can either be files or
    aliases (starting with `@`), interpreted in the current working directory.
    Path translation is done automatically if `cwd` is given.

    @param targets: the targets to build
    @param cwd: alternative current working directory (optional)
    @raises ValueError: in case of ill-formed target
    @raises DuneError: in case of build failure
    """
    if not targets:
        return

    def make_target(target: str) -> str:
        return _build_target(_relative_target(_parse_target(target), cwd))

    args = ["build", "--no-print-directory", "--display=quiet"]
    _ = _run_dune(args + [make_target(t) for t in targets], cwd)


def dune_env_hack() -> dict[str, str]:
    """
    Builds an environment that disables dune's locking mechanism.

    @returns: an extended copy of the environment
    """
    env_copy: dict[str, str] = os.environ.copy()
    env_copy["DUNE_CONFIG__GLOBAL_LOCK"] = "disabled"
    return env_copy


def _rocq_args(file: Path, cwd: str | Path | None, build: bool) -> list[str]:
    # The dune environment hack is not needed for `dune rocq top`.
    args = [
        "rocq",
        "top",
        *(["--no-build"] if not build else []),
        "--no-print-directory",
        "--display=quiet",
        "--toplevel=rocq-fake-repl",
        str(_canonical_rel_path(file, cwd)),
    ]
    return [x.strip() for x in _run_dune(args, cwd).splitlines()]


def _iter_path_args(
    args: list[str],
) -> Iterator[tuple[Literal["I"], str] | tuple[Literal["Q"], str, str]]:
    nb_args = len(args)
    for i in range(nb_args):
        opt = args[i]
        if opt == "-I" and i < nb_args - 1:
            yield ("I", args[i + 1])
        if (opt == "-Q" or opt == "-R") and i < nb_args - 2:
            yield ("Q", args[i + 1], args[i + 2])


def _extra_args(args: list[str], extra_args: list[list[str]]) -> list[str]:
    covered_i: set[str] = set()
    covered_q: set[str] = set()
    for arg in _iter_path_args(args):
        if arg[0] == "I":
            covered_i.add(arg[1])
        if arg[0] == "Q":
            covered_q.add(arg[1])
    new_args = []
    for args in extra_args:
        for arg in _iter_path_args(args):
            if arg[0] == "I":
                d = arg[1]
                if d not in covered_i:
                    covered_i.add(d)
                    new_args.append("-I")
                    new_args.append(d)
            if arg[0] == "Q":
                d = arg[1]
                m = arg[2]
                if d not in covered_q:
                    covered_q.add(d)
                    new_args.append("-Q")
                    new_args.append(d)
                    new_args.append(m)
    return new_args


class DuneRocqPluginNotFound(Exception):
    """Exception raised if a plugin cannot be found."""

    pass


class DuneRocqPlugin:
    """
    Specification of a dune Rocq Plugin. Such plugins can be requested while
    computing command-line arguments, and they are resolved based on their
    opam package name (and ocamlfind package).
    """

    def __init__(
        self,
        *,
        opam_pkg: str,
        entry_points: list[str],
        findlib_pkg: str | None = None,
    ) -> None:
        """
        @param opam_pkg: name of the opam package for the plugin
        @param entry_points: relative paths to Rocq sources under the package
        @param findlib_pkg: findlib package name (defaults to `opam_pkg`)
        """
        self.opam_pkg = opam_pkg
        self.entry_points = entry_points
        self.findlib_pkg = opam_pkg if findlib_pkg is None else findlib_pkg

    def locate_in_workspace(self, source_root: Path) -> Path | None:
        """
        Tries to locate the plugin's main directory under the dune workspace
        whose root is specified by `source_root`.

        @param source_root: root of the dune workspace to explore
        @returns: a relative path from `source_root` if the plugin is located
        """
        opam_file = f"{self.opam_pkg}.opam"
        excluded_dirs = {".git", "_build"}
        opam_files = source_root.rglob(opam_file, recurse_symlinks=True)
        candidate_dirs = [
            file.parent
            for file in opam_files
            if not any(d in file.parts for d in excluded_dirs)
        ]
        # NOTE: dune would complain if there was more than one.
        assert len(candidate_dirs) < 2
        if len(candidate_dirs) == 1:
            return candidate_dirs[0]
        return None

    def is_installed(self, source_root: Path) -> bool:
        """
        Indicates whether the plugin is installed, based on ocamlfind. To make
        sure that the package is searched for in the right opam switch, the
        query is run from the given `source_root`.

        @param source_root: root of the dune workspace
        @returns: boolean indicating if the plugin is installed
        """
        args = ["query", "-qo", "-qe", self.findlib_pkg]
        res = subprocess.run(
            ["opam", "exec", "--", "ocamlfind"] + args,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            cwd=str(source_root),
        )
        return res.returncode == 0

    def resolve(self, source_root: Path) -> list[str]:
        """
        Resolves the plugin to Rocq files paths relative to `source_root`. If
        the plugin is not in the workspace, an empty list of files is given,
        and it is checked that the package is available in an installed form.
        Installed plugins are currently always available to Rocq, so we don't
        need to do anything specific for Rocq to have access to them.

        @param source_root: root of the dune workspace
        @returns: list of paths to Rocq sources, relative to `source_root`
        """
        path = self.locate_in_workspace(source_root)
        if path is None:
            if self.is_installed(source_root):
                return []
            raise DuneRocqPluginNotFound(
                f"Cannot locate the plugin (opam package) '{self.opam_pkg}'."
            )
        return [str(path / file) for file in self.entry_points]


def rocq_args_for(
    file: str | Path,
    *,
    cwd: str | Path | None = None,
    build: bool = False,
    extra_deps: list[str | Path] | None = None,
    workspace_deps: list[str | Path] | None = None,
    plugins: list[DuneRocqPlugin] | None = None,
) -> list[str]:
    """
    Give the Rocq command line arguments that are needed to build / process
    the given Rocq source file. If `extra_deps` and/or `workspace_deps` is
    given, the returned Rocq arguments are guaranteed to be suitable for
    "Require"-ing the corresponding Rocq modules in the file, even if it does
    not depend on them explicitly.

    @param file: the Rocq source file for which arguments are being produced.
        Path should be relative to the current working directory (NOT `cwd`).
    @param cwd: alternative current working directory (optional)
    @param build: should the dependencies of `file` and `extra_deps` be built?
    @param extra_deps: additional Rocq files to be made available
    @param workspace_deps: same with paths relative to the dune workspace root
    @param plugins: same but specified via a plugin (installed or not)
    @returns: the command line arguments
    @raises ValueError: if the provided files don't have the ".v" suffix
    @raises DuneError: if command line arguments cannot be collected
    @raises DuneRocqPluginNotFound: if a plugin cannot be located
    """

    # Validate the input files.
    def check_v_file(file: str | Path) -> Path:
        path = Path(file)
        if path.suffix != ".v":
            raise ValueError(f"Expected Rocq source file, given {str(path)}")
        return path

    path: Path = check_v_file(file)

    source_root: Path | None = None

    # Resolving the extra dependencies.
    deps: list[Path] = []
    for file in extra_deps if extra_deps else []:
        deps.append(check_v_file(file))

    # Resolving the workspace dependencies.
    if workspace_deps:
        if source_root is None:
            source_root = dune_sourceroot(cwd=cwd)
        for file in workspace_deps:
            rel = check_v_file(file)
            if rel.is_absolute():
                raise ValueError(f"Expected relative path, given {str(rel)}")
            deps.append(source_root / rel)

    # Resolving the plugins.
    if plugins:
        if source_root is None:
            source_root = dune_sourceroot(cwd=cwd)
        for plugin in plugins:
            for dep in plugin.resolve(source_root):
                deps.append(source_root / dep)

    # Build the extra dependencies if needed. Note that the dependencies of
    # the main file are built separately, when calling `_rocq_args`, as there
    # is not way to build its dependencies only in a call to `dune build`.
    if build and deps:
        targets = [str(file.with_suffix(".vo")) for file in deps]
        dune_build(targets, cwd=cwd)

    # Getting command-line arguments for the file and the extra dependencies.
    rocq_args = _rocq_args(path, cwd, build)
    extra_args = [_rocq_args(dep, cwd, False) for dep in deps]
    if extra_args:
        rocq_args = rocq_args + _extra_args(rocq_args, extra_args)

    return rocq_args

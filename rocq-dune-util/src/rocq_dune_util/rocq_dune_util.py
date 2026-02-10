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
    return path.resolve().relative_to(rel_base.resolve(), walk_up=True)


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


def rocq_args_for(
    file: str | Path,
    *,
    cwd: str | Path | None = None,
    build: bool = False,
    extra_deps: list[str | Path] | None = None,
    workspace_deps: list[str | Path] | None = None,
) -> list[str]:
    """
    Give the Rocq command line arguments that are needed to build / process
    the given Rocq source file. If `extra_deps` and/or `workspace_deps` is
    given, the returned Rocq arguments are guanranteed to be suitable for
    "Require"-ing the corresponding Rocq modules in the file, even if it does
    not depend on them explicitly.

    @param file: the Rocq source file for which arguments are being produced
    @param cwd: alternative current working directory (optional)
    @param build: should the dependencies of `file` and `extra_deps` be built?
    @param extra_deps: additional Rocq files to be made available
    @param workspace_deps: same with paths relative to the dune workspace root
    @returns: the command line arguments
    @raises ValueError: if the provided files don't have the ".v" suffix
    @raises DuneError: if command line arguments cannot be collected
    """

    # Validate the input files.
    def check_v_file(file: str | Path) -> Path:
        path = Path(file)
        if path.suffix != ".v":
            raise ValueError(f"Expected Rocq source file, given {str(path)}")
        return path

    path: Path = check_v_file(file)

    # Resolving the extra dependencies.
    deps: list[Path] = []
    for file in extra_deps if extra_deps else []:
        deps.append(check_v_file(file))
    if workspace_deps:
        source_root = dune_sourceroot(cwd=cwd)
        for file in workspace_deps:
            rel = check_v_file(file)
            if rel.is_absolute():
                raise ValueError(f"Expected relative path, given {str(rel)}")
            deps.append(source_root / rel)

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

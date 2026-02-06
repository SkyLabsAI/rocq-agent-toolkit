import os
import subprocess
from collections.abc import Iterator
from pathlib import Path
from typing import Literal


class DuneError(Exception):
    def __init__(self, *, stdout: str, stderr: str) -> None:
        self.stdout = stdout
        self.stderr = stderr


def _run_dune(args: list[str], cwd: Path | None) -> str:
    res = subprocess.run(
        ["dune"] + args,
        capture_output=True,
        cwd=str(cwd) if cwd is not None else None,
    )
    stdout = res.stdout.decode(encoding="utf-8")
    if res.returncode != 0:
        stderr = res.stderr.decode(encoding="utf-8")
        raise DuneError(stdout=stdout, stderr=stderr)
    return stdout


def dune_sourceroot(*, cwd: Path | None = None) -> Path:
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


def dune_build(targets: list[str], *, cwd: Path | None = None) -> None:
    """
    Builds the given targets using dune. The targets, if they refer to files,
    must be relative to the current working directory (or to `cwd` if given).

    @param targets: the targets to build
    @param cwd: alternative current working directory (optional)
    @raises DuneError: in case of build failure
    """
    args = ["build", "--no-print-directory", "--display=quiet"] + targets
    _ = _run_dune(args, cwd)


def dune_env_hack() -> dict[str, str]:
    """
    Builds an environment that disables dune's locking mechanism.

    @returns: an extended copy of the environment
    """
    env_copy: dict[str, str] = os.environ.copy()
    env_copy["DUNE_CONFIG__GLOBAL_LOCK"] = "disabled"
    return env_copy


def _rocq_args_for(file: Path, cwd: Path | None, build: bool) -> list[str]:
    # The dune environment hack is not needed for `dune rocq top`.
    args = [
        "rocq",
        "top",
        *(["--no-build"] if not build else []),
        "--no-print-directory",
        "--display=quiet",
        "--toplevel=rocq-fake-repl",
        str(file),
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
    cwd: Path | None = None,
    build: bool = False,
    extra_deps: list[str | Path] | None = None,
) -> list[str]:
    """
    Give the Rocq command line arguments that are needed to build / process
    the given Rocq source file. If `extra_deps` is given, the returned Rocq
    arguments are ensured to be suitable for "Require"-ing the corresponding
    Rocq modules in the file, even if it does not depend on them. Note that
    the paths in `extra_deps` should be relative to the dune source root.

    @param file:
    @param cwd:
    @param build:
    @param extra_deps:
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
    deps: list[Path] = []

    # Resolving the extra dependencies.
    if extra_deps:
        deps = [check_v_file(file) for file in extra_deps]
        source_root = dune_sourceroot(cwd=cwd)
        rel_base = cwd if cwd is not None else Path(".")

        def resolve(path: Path) -> Path:
            absolute = source_root / path
            return absolute.relative_to(rel_base.resolve(), walk_up=True)

        deps = [resolve(path) for path in deps]

    # Build the extra dependencies if needed.
    if build and deps:
        targets = [str(file.with_suffix(".vo")) for file in deps]
        dune_build(targets, cwd=cwd)

    # Getting command-line arguments for the file and the extra dependencies.
    rocq_args = _rocq_args_for(path, cwd, build)
    extra_args = [_rocq_args_for(path, cwd, False) for path in deps]

    if extra_args:
        rocq_args = rocq_args + _extra_args(rocq_args, extra_args)

    # Combining the arguments.
    return rocq_args

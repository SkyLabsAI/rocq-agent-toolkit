import itertools
import logging
import re
import sys
from argparse import ArgumentParser, Namespace
from collections import defaultdict
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal

import git
import sexpdata  # type: ignore
from rocq_doc_manager import RocqCursor, RocqDocManager
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_doc_manager.locator import FirstLemma
from rocq_dune_util import DuneError, rocq_args_for

from rocq_pipeline.args_util import valid_file
from rocq_pipeline.taggers.tactic_tagger import extract_tactics
from rocq_pipeline.tasks import Project, Task, TaskFile
from rocq_pipeline.util import parallel_runner

logger = logging.getLogger(__name__)


@dataclass
class ProofTask:
    start: int
    end: int
    final: Literal["aborted", "qed", "admitted"]
    proof_tactics: list[str]


def scan_proof(suffix: list[rdm_api.SuffixItem]) -> ProofTask:
    tactics: list[str] = []
    start = 0
    for i, sentence in enumerate(suffix):
        if sentence.kind != "command":
            continue
        txt: str = sentence.text
        if txt.startswith("Proof"):
            start = i + 1
        elif txt.startswith("Qed") or txt.startswith("Defined"):
            return ProofTask(start, i, "qed", tactics)
        elif txt.startswith("Abort"):
            return ProofTask(start, i, "aborted", tactics)
        elif txt.startswith("Admitted"):
            return ProofTask(start, i, "admitted", tactics)
        else:
            tactics.append(txt)
    raise ValueError("Failed to find the end of the proof")


def find_tasks(
    pdir: Path,
    path: Path,
    args: list[str],
    tagger: Callable[[ProofTask], set[str]] | None = None,
) -> list[Task]:
    """Find the tasks in the given file. Invoke the tagger argument to generate the tags."""
    with RocqDocManager(args, str(path.absolute()), chdir=str(pdir), dune=True).sess(
        load_file=True
    ) as rdm:
        rc: RocqCursor = rdm.cursor()
        tasks: list[Task] = []
        counts: dict[str, int] = defaultdict(int)

        suffix = rc.doc_suffix()
        total_sentences = len(suffix)
        idx = 0
        mtch = re.compile("(Lemma|Theorem)\\s+([0-9a-zA-Z_']+)[^0-9a-zA-Z_]")
        while idx < total_sentences:
            logger.debug(f"Running at index {idx}")
            sentence = suffix[idx]
            idx += 1
            if sentence.kind != "command":
                continue
            m = mtch.match(sentence.text)
            if m is not None:
                canon_name = f"{m.group(1)}:{m.group(2)}"
                current = counts[canon_name]
                counts[canon_name] += 1
                try:
                    proof: ProofTask = scan_proof(suffix[idx:])
                    idx += proof.end
                    tags = {"proof"}
                    if tagger is not None:
                        tags.update(tagger(proof))
                except ValueError as err:
                    logger.error(
                        f"In file {path}, no end found for {m.group(1)} {m.group(2)}.\n"
                        f"From {err}"
                    )
                    # tags = {"proof", "incomplete"}
                    break
                locator = FirstLemma(m.group(2), m.group(1), current)
                file = path.relative_to(pdir)
                task = Task(
                    name=None, file=file, locator=locator, tags=tags, prompt=None
                )
                tasks.append(task)

        return tasks


def my_tagger(task: ProofTask) -> set[str]:
    tags: set[str] = set()
    numtactics = 0
    omitted: set[str] = set()

    for sentence in task.proof_tactics:
        identified_tactics: dict[str, int]
        leftovers: list[str]
        identified_tactics, leftovers = extract_tactics(sentence)

        # increment numtactics by adding the identified_tactics according to their multiplicities
        numtactics = numtactics + sum(identified_tactics.values())

        # add the identified tactics to tags, ignoring entries with non-positive multiplicities
        has_nonpositives = any(value < 1 for value in identified_tactics.values())

        tactics: set[str]
        if has_nonpositives:
            logger.debug("Eliminating the tactics with multiplicity < 1.")
            tactics = {key for key, value in identified_tactics.items() if value > 0}
        else:
            tactics = set(identified_tactics.keys())

        tags.update(tactics)
        omitted.update(set(leftovers))

    tags.add(f"NumTactics={numtactics}")

    tags.add(task.final)

    if omitted:
        tags.add(f"UnmatchedTactics={sorted(omitted)}")

    return tags


def mk_parser(parent: Any | None = None) -> Any:
    help = "Ingest a Rocq (dune) project to build a corresponding task file."
    description = "This command ingests the Rocq source files of a Rocq (dune) project to produce a task file, either in JSON or Yaml format (based on the file's extension). A task file contains information about the originating project (git URL and commit hash), including the path to the project relative to the task file's parent directory, so that subsequent rat commands can automatically locate the project. It also contains a list of task, each of which applies to a specific Rocq source file identified by a relative path from the project's root directory. For now, all the generated tasks concern proofs, and are thus meant to be tackled by proof agents. We aim at collecting other forms of tasks in the future."
    if parent:
        parser = parent.add_parser("ingest", help=help, description=description)
    else:
        parser = ArgumentParser(description=description)

    parser.add_argument(
        "-v",
        "--verbose",
        action="store_true",
        help="make the output verbose (including logs)",
    )

    parser.add_argument(
        "-d",
        "--debug",
        action="store_true",
        help="enable debug output (implies --verbose)",
    )

    parser.add_argument(
        "-o",
        "--output",
        metavar="FILE",
        type=valid_file(
            check_creatable=True, allowed_suffixes=TaskFile.supported_extensions()
        ),
        required=True,
        help=f"specify the output file (allowed extensions are {', '.join(TaskFile.supported_extensions())})",
    )

    parser.add_argument(
        "-j",
        "--jobs",
        metavar="N",
        type=lambda N: max(1, int(N)),
        default=1,
        help="number of parallel workers (1 by default)",
    )

    def check_pdir(dir: str) -> Path:
        path = Path(dir)
        if not path.exists():
            sys.exit(f"Error: directory {path} does not exist.")
        if not path.is_dir():
            sys.exit(f"Error: file {path} is not a directory.")
        dune_project = path / "dune-project"
        if not dune_project.exists():
            sys.exit(f'Error: no dune-project file in directory "{path}".')
        return path

    parser.add_argument(
        "-p",
        "--pdir",
        metavar="DIR",
        type=check_pdir,
        default=Path("."),
        help="path to the dune project to ingest (directory containing dune-project)",
    )

    def check_rocq_files(file: str) -> Path:
        path = Path(file)
        if not path.exists():
            sys.exit(f"Error: file {path} does not exist.")
        if path.suffix != ".v":
            sys.exit(f'Error: file {path} does not have ".v" extension.')
        return path

    parser.add_argument(
        "rocq_files",
        metavar="ROCQ_FILE",
        type=valid_file(exists=True, allowed_suffixes=[".v"]),
        nargs="*",
        help="file to be ingested (all files are ingested if none is given)",
    )

    return parser


def dune_project_name(dune_project_file: Path) -> str | None:
    try:
        contents = dune_project_file.read_text()
        data = sexpdata.loads(f"({contents})")
        for e in data:
            if not (isinstance(e, list) and len(e) == 2):
                continue
            key = e[0].value()
            if not (isinstance(key, str) or key != "name"):
                continue
            value = e[1].value()
            if not (isinstance(value, str)):
                continue
            return value
    except FileNotFoundError:
        sys.exit(f"Error: project file {dune_project_file} not found.")
    except Exception as e:
        sys.exit(f"Error: file {dune_project_file} could not be parsed.")
    return None


def git_repo_data(project_dir: Path) -> tuple[str, str]:
    try:
        repo = git.Repo(project_dir, search_parent_directories=True)
    except Exception:
        logger.warn("The project does not seem to use git for versioning.")
        return ("unknown", "unknown")
    try:
        url = repo.remotes.origin.url
    except Exception:
        logger.warn("No origin remote set, unable to find a git URL.")
        url = "unknown"
    try:
        commit = repo.head.commit.hexsha
        if repo.is_dirty(untracked_files=True):
            commit = commit + "-dirty"
    except Exception:
        logger.warn("The current commit hash could not be determined.")
        commit = "unknown"
    return (url, commit)


def run(output_file: Path, pdir: Path, rocq_files: list[Path], jobs: int = 1) -> None:
    def run_it(path: Path, _: Any) -> list[Task]:
        try:
            file = Path(path)
            args = rocq_args_for(file, cwd=pdir)
            file_tasks: list[Task] = find_tasks(pdir, file, args, tagger=my_tagger)
        except DuneError as e:
            logger.error(f"Unable to get CLI arguments for file {path}: {e.stderr}")
            return []
        except Exception as err:
            logger.error(f"Error occured while scanning file {path}. {err}")
            file_tasks = []
        logger.info(
            f"Found {len(file_tasks)} tasks in {path}: "
            + ", ".join([str(x.locator) for x in file_tasks[0:3]])
            + (", ..." if len(file_tasks) > 3 else "")
        )
        return file_tasks

    project_name = dune_project_name(pdir / "dune-project")
    if project_name is None:
        project_name = pdir.resolve().name
        logger.warn(
            f"No project name in the dune-project file, falling back to directory name {project_name}."
        )
    logger.debug(f"Detected project name: {project_name}")

    (git_url, git_commit) = git_repo_data(pdir)
    logger.debug(f"Detected git URL: {git_url}")
    logger.debug(f"Detected git commit: {git_commit}")

    exclude = {"_build", ".git", "_opam"}
    project_files = [
        p for p in pdir.rglob("*.v") if not any(part in exclude for part in p.parts)
    ]
    logger.info(f"Number of Rocq source files found: {len(project_files)}")
    if len(project_files) == 0:
        logger.warning("No Rocq source files found in the project.")

    for file in rocq_files:
        if not any(Path(p).samefile(file) for p in project_files):
            sys.exit(f"Error: file {file} is not part of the project.")

    if len(rocq_files) != 0:
        logger.info("Only keeping the files passed on the command line.")
        project_files = rocq_files

    for file in project_files:
        logger.debug(f"Will ingest file {file}")

    all_tasks: list[list[Task]] = parallel_runner(
        run_it, [(str(x), x) for x in project_files], None, jobs=jobs, progress=False
    )
    flat_tasks = list(itertools.chain.from_iterable(all_tasks))
    logger.info(f"Total number of tasks: {len(flat_tasks)}")

    unique_tasks: list[Task] = []
    seen_tasks: set[tuple[str, str]] = set()

    for d in flat_tasks:
        t = (str(d.file), str(d.locator))
        if t not in seen_tasks:
            seen_tasks.add(t)
            unique_tasks.append(d)

    logger.info(f"Total number of unique tasks: {len(unique_tasks)}")

    project = Project(
        name=project_name, git_url=git_url, git_commit=git_commit, path=pdir
    )
    taskfile = TaskFile.from_bundles([(project, unique_tasks)])

    logger.debug(f"Saving tasks to {output_file}")
    taskfile.to_file(output_file)


def run_ns(args: Namespace, extra_args: list[str] | None = None) -> None:
    assert extra_args is None or len(extra_args) == 0
    log_level = (
        logging.DEBUG
        if args.debug
        else logging.INFO
        if args.verbose
        else logging.WARNING
    )
    logging.basicConfig(level=log_level, format="%(levelname)s: %(message)s")
    return run(args.output, args.pdir, args.rocq_files, jobs=args.jobs)


def main() -> None:
    args = mk_parser().parse_args()
    run_ns(args)

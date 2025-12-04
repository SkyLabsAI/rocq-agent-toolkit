import itertools
import json
import re
import sys
from argparse import ArgumentParser, Namespace
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import yaml
from rocq_doc_manager import DuneUtil, RocqDocManager

from rocq_pipeline.locator import NotFound
from rocq_pipeline.taggers import tactic_tagger
from rocq_pipeline.util import parallel_runner


@dataclass
class ProofTask:
    start: int
    end: int
    admitted: bool
    proof_tactics: list[str]

def scan_proof(suffix : list[RocqDocManager.SuffixItem]) -> ProofTask:
    tactics: list[str] = []
    start = 0
    for i, sentence in enumerate(suffix):
        if sentence.kind != "command":
            continue
        txt: str = sentence.text
        if txt.startswith("Proof"):
            start = i+1
            continue
        proof_ended: bool = (
            txt.startswith("Qed") or
            txt.startswith("Admitted") or
            txt.startswith("Abort") or
            txt.startswith("Defined")
        )
        if proof_ended:
            return ProofTask(start, i, not txt.startswith("Qed"), tactics)
        tactics.append(txt)
    raise NotFound

def find_tasks(path : Path, tagger: Callable[[ProofTask], set[str]] | None = None) -> list[dict[str, Any]]:
    """Find the tasks in the given file. Invoke the tagger argument to generate the tags."""
    with RocqDocManager(DuneUtil.rocq_args_for(path), str(path), dune=True).sess(load_file=True) as rdm:
        tasks = []

        suffix = rdm.doc_suffix()
        total_sentences = len(suffix)
        idx = 0
        mtch = re.compile("(Lemma|Theorem)\\s+([0-9a-zA-Z_']+)[^0-9a-zA-Z_]")
        while idx < total_sentences:
            sentence = suffix[idx]
            idx += 1
            if sentence.kind != "command":
                continue
            m = mtch.match(sentence.text)
            if m is not None:
                try:
                    proof: ProofTask = scan_proof(suffix[idx:])
                    idx += proof.end
                    tags = {"proof"}
                    if tagger is not None:
                        tags.update(tagger(proof))
                except NotFound:
                    print(f"{m.group(1)} {m.group(2)} does not end", file=sys.stderr)
                    tags = {"proof", "incomplete"}
                task_json = { "locator": f"{m.group(1)}:{m.group(2)}", "tags": list(tags)}
                tasks.append(task_json)
                continue
        return tasks

def my_tagger(task: ProofTask) -> set[str]:
    tags:set[str] = set()
    numtactics = 0
    omitted:set[str] = set()

    for sentence in task.proof_tactics:
        identified_tactics, leftovers = tactic_tagger.extract_tactics(sentence)

        #increment numtactics by adding the identified_tactics according to their multiplicities
        numtactics = numtactics + sum(identified_tactics.values())

        #add the identified tactics to tags, ignoring entries with non-positive multiplicities
        nonzero_identifed_tactics: set[str] = {key for key, value in identified_tactics.items() if value > 0}
        tags.update(nonzero_identifed_tactics)
        omitted.update(set(leftovers))

    tags.add(f'NumTactics={numtactics}')

    if task.admitted:
        tags.add("admitted")

    if omitted:
        tags.add(f'UnmatchedTactics={sorted(omitted)}')

    return tags

def mk_parser(parent: Any|None=None) -> Any:
    # 1. Create the parser
    if parent:
        parser = parent.add_parser("ingest", help="Build tasks from Rocq files.")
    else:
        parser = ArgumentParser(description="Build tasks from Rocq files.")

    def check_file_name(file_path: str) -> Path:
        s: Path = Path(file_path)
        if s.suffix in [".yml", ".yaml", ".json"]:
            return s
        print(f"Unknown file type: {s}", file=sys.stderr)
        exit(1)

    # 2. Add the optional argument: -o/--output
    # 'dest' sets the name of the attribute in the returned namespace
    # 'required=True' can be used if the argument must be present (but you asked for an 'option')
    parser.add_argument(
        '-o', '--output',
        type=check_file_name,
        default='tasks.yaml', # A default value if the option is not provided
        help='Specify the name of the output file. (e.g., -o tasks.yaml)'
    )
    parser.add_argument(
        "-j", "--jobs",
        type=lambda N: max(1, int(N)),
        default=1,
        help="The number of parallel workers."
    )

    # 3. Add the positional arguments
    # 'nargs='+' means one or more positional arguments are required
    # 'nargs='*' means zero or more positional arguments are allowed
    parser.add_argument(
        'rocq_files',
        type=str,
        nargs='+', # Accepts an arbitrary number of arguments (one or more)
        help='The Rocq files to parse. (e.g. foo.v test/bar.v)'
    )

    return parser

def run(output_file: Path, rocq_files: list[Path], jobs:int=1) -> None:
    def run_it(path: Path, _:Any) -> list[dict[str,Any]]:
        try:
            file_tasks: list[dict[str, Any]] = find_tasks(Path(path), tagger=my_tagger)
            print(f"Found {len(file_tasks)} tasks in {path}: {[x['locator'] for x in file_tasks]}")
            for y in file_tasks:
                y["file"] = path
            return file_tasks
        except RuntimeError as err:
            print(f"Error occured while scanning file {path}. {err}")
            return []

    all_tasks:list[list[dict[str, Any]]] = parallel_runner(run_it, [(str(x),x) for x in rocq_files], None, jobs=jobs, progress=False)
    flat_tasks = list(itertools.chain.from_iterable(all_tasks))
    print(f"Total number of tasks: {len(flat_tasks)}")
    with open(output_file, 'w') as f:
        if output_file.suffix in [".yml", ".yaml"]:
            yaml.dump(flat_tasks, f)
        elif output_file.suffix == ".json":
            json.dump(flat_tasks, f)
        else:
            print(f"unknown file format! {output_file}")

def run_ns(args: Namespace, extra_args:list[str]|None=None) -> None:
    assert extra_args is None or len(extra_args) == 0
    return run(args.output, args.rocq_files, jobs=args.jobs)

def main() -> None:
    args = mk_parser().parse_args()
    run_ns(args)

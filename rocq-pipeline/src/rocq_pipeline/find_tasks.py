import argparse
import json
import re
import sys
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import yaml
from rocq_doc_manager import DuneUtil, RocqDocManager

from rocq_pipeline.locator import NotFound


@dataclass
class ProofTask:
    start: int
    end: int
    admitted: bool
    proof_tactics: list[str]

def scan_proof(suffix : list[dict[str, Any]]) -> ProofTask:
    tactics: list[str] = []
    start = 0
    for i, sentence in enumerate(suffix):
        if sentence["kind"] != "command":
            continue
        txt: str = sentence["text"]
        if txt.startswith("Proof"):
            start = i
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

def find_tasks(path : Path, tagger: Callable[[ProofTask], list[str]] | None = None) -> list[dict[str, Any]]:
    """Find the tasks in the given file. Invoke the tagger argument to generate the tags."""
    rdm = RocqDocManager(DuneUtil.rocq_args_for(path), str(path), dune=True)
    assert isinstance(rdm.load_file(), rdm.Resp)

    tasks = []

    suffix = rdm.doc_suffix()
    total_sentences = len(suffix)
    idx = 0
    mtch = re.compile("(Lemma|Theorem)\\s+([0-9a-zA-Z_']+)[^0-9a-zA-Z_]")
    while idx < total_sentences:
        sentence: dict[str,str] = suffix[idx]
        idx += 1
        if sentence["kind"] != "command":
            continue
        m = mtch.match(sentence["text"])
        if m is not None:
            try:
                proof: ProofTask = scan_proof(suffix[idx:])
                idx += proof.end
                tags = ["proof"]
                if tagger is not None:
                    tags.extend(tagger(proof))
            except NotFound:
                print(f"Lemma {m.group(2)} does not end", file=sys.stderr)
                tags = ["proof", "incomplete"]
            task_json = { "locator": f"lemma:{m.group(2)}", "tags": tags}
            tasks.append(task_json)
            continue
    rdm.quit()
    return tasks

def my_tagger(task: ProofTask) -> list[str]:
    tags = ["admitted"] if task.admitted else []
    def contains(pred: Callable[[Any], bool], ls: list[Any]) -> bool:
        for x in ls:
            if pred(x):
                return True
        return False
    if contains(lambda x: x.startswith('verify_spec'), task.proof_tactics):
        tags.append("brick")
    if contains(lambda x: x.startswith('wp_for'), task.proof_tactics):
        tags.append('for-loop')
    if contains(lambda x: x.startswith('wp_while'), task.proof_tactics):
       tags.append('while-loop')
    if contains(lambda x: x.startswith('wp_do'), task.proof_tactics):
        tags.append('do-loop')
    return tags

def parse_arguments() -> argparse.Namespace:
    # 1. Create the parser
    parser = argparse.ArgumentParser(
        description="Build task files from Rocq sources."
    )

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

    # 4. Parse the arguments from sys.argv
    # By default, parse_args() uses sys.argv[1:]
    args = parser.parse_args()

    return args

def main() -> None:
    all_tasks: list[dict[str, Any]] = []
    args = parse_arguments()
    with ThreadPoolExecutor(args.jobs) as tpe:
        def run_it(path: str) -> list[dict[str,Any]]:
            file_tasks: list[dict[str, Any]] = find_tasks(Path(path), tagger=my_tagger)
            print(f"Found {len(file_tasks)} tasks in {path}: {[x['locator'] for x in file_tasks]}")
            for y in file_tasks:
                y["file"] = path
            return file_tasks
        for result in tpe.map(run_it, args.rocq_files):
            all_tasks.extend(result)

    with open(args.output, 'w') as f:
        if args.output.suffix in [".yml", ".yaml"]:
            yaml.dump(all_tasks, f)
        elif args.output.suffix == ".json":
            json.dump(all_tasks, f)
        else:
            print(f"unknown file format! {args.output}")

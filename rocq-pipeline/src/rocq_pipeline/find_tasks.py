import itertools
import json
import os
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

def find_tasks(path : Path, tagger: Callable[[ProofTask], list[str]] | None = None) -> list[dict[str, Any]]:
    """Find the tasks in the given file. Invoke the tagger argument to generate the tags."""
    rdm = RocqDocManager(DuneUtil.rocq_args_for(path), str(path), dune=True)
    resp = rdm.load_file()
    if isinstance(resp, RocqDocManager.Err):
        print(f"Loading file failed with error (pwd={os.curdir}):\n{resp}")
        raise RuntimeError(f"Failed to load file: {resp}")

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
    if contains(lambda x: x.startswith('rewrite'), task.proof_tactics):
        tags.append('rewrite')
    if contains(lambda x: x.startswith('erewrite'), task.proof_tactics):
        tags.append('erewrite')
    if contains(lambda x: x.startswith('by rewrite'), task.proof_tactics):
        tags.append('rewrite')
    if contains(lambda x: x.startswith('bind_ren'), task.proof_tactics):
        tags.append('bind_ren')
    if contains(lambda x: x.startswith('ren_hyp'), task.proof_tactics):
        tags.append('ren_hyp')
    if contains(lambda x: x.startswith('apply'), task.proof_tactics):
        tags.append('apply')
    if contains(lambda x: x.startswith('eapply'), task.proof_tactics):
        tags.append('eapply')
    if contains(lambda x: x.startswith('by apply'), task.proof_tactics):
        tags.append('apply')
    if contains(lambda x: x.startswith('case_decide'), task.proof_tactics):
        tags.append('case_decide')
    if contains(lambda x: x.startswith('assert'), task.proof_tactics):
        tags.append('assert')
    if contains(lambda x: x.startswith('simpl'), task.proof_tactics):
        tags.append('simpl')
    if contains(lambda x: x.startswith('Arith.arith_simpl'), task.proof_tactics):
        tags.append('Arith.arith_simpl')
    if contains(lambda x: x.startswith('trivial'), task.proof_tactics):
        tags.append('trivial')
    if contains(lambda x: x.startswith('reflexivity'), task.proof_tactics):
        tags.append('reflexivity')
    if contains(lambda x: x.startswith('cbn'), task.proof_tactics):
        tags.append('cbn')
    if contains(lambda x: x.startswith('subst'), task.proof_tactics):
        tags.append('subst')
    if contains(lambda x: x.startswith('clear'), task.proof_tactics):
        tags.append('clear')
    if contains(lambda x: x.startswith('replace'), task.proof_tactics):
        tags.append('replace')
    if contains(lambda x: x.startswith('specialize'), task.proof_tactics):
        tags.append('specialize')
    if contains(lambda x: x.startswith('intro'), task.proof_tactics):
        tags.append('intro')
    if contains(lambda x: x.startswith('destruct'), task.proof_tactics):
        tags.append('destruct')
    if contains(lambda x: x.startswith('inversion'), task.proof_tactics):
        tags.append('inversion')
    if contains(lambda x: x.startswith('exists'), task.proof_tactics):
        tags.append('exists')
    if contains(lambda x: x.startswith('exfalso'), task.proof_tactics):
        tags.append('exfalso')
    if contains(lambda x: x.startswith('lia'), task.proof_tactics):
        tags.append('lia')
    if contains(lambda x: x.startswith('by lia'), task.proof_tactics):
        tags.append('lia')
    if contains(lambda x: x.startswith('assumption'), task.proof_tactics):
        tags.append('assumption')
    if contains(lambda x: x.startswith('by assumption'), task.proof_tactics):
        tags.append('assumption')
    if contains(lambda x: x.startswith('eassumption'), task.proof_tactics):
        tags.append('eassumption')
    if contains(lambda x: x.startswith('remember'), task.proof_tactics):
        tags.append('remember')
    if contains(lambda x: x.startswith('symmetry'), task.proof_tactics):
        tags.append('symmetry')
    if contains(lambda x: x.startswith('unfold'), task.proof_tactics):
        tags.append('unfold')
    if contains(lambda x: x.startswith('f_equal'), task.proof_tactics):
        tags.append('f_equal')
    if contains(lambda x: x.startswith('constructor'), task.proof_tactics):
        tags.append('constructor')
    if contains(lambda x: x.startswith('induction'), task.proof_tactics):
        tags.append('induction')
    if contains(lambda x: x.startswith('intuition'), task.proof_tactics):
        tags.append('intuition')
    if contains(lambda x: x.startswith('iExists'), task.proof_tactics):
        tags.append('iExists')
    if contains(lambda x: x.startswith('iAssert'), task.proof_tactics):
        tags.append('iAssert')
    if contains(lambda x: x.startswith('revert'), task.proof_tactics):
        tags.append('revert')
    if contains(lambda x: x.startswith('left'), task.proof_tactics):
        tags.append('left')
    if contains(lambda x: x.startswith('right'), task.proof_tactics):
        tags.append('right')
    if contains(lambda x: x.startswith('Opaque'), task.proof_tactics):
        tags.append('Opaque')
    if contains(lambda x: x.startswith('Transparent'), task.proof_tactics):
        tags.append('Transparent')
    if contains(lambda x: x.startswith('Search'), task.proof_tactics):
        tags.append('Search')
    if contains(lambda x: x.startswith('Print'), task.proof_tactics):
        tags.append('Print')
    if contains(lambda x: x.startswith('Check'), task.proof_tactics):
        tags.append('Check')
    if contains(lambda x: x.startswith('admit'), task.proof_tactics):
        tags.append('admit')
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
        file_tasks: list[dict[str, Any]] = find_tasks(Path(path), tagger=my_tagger)
        print(f"Found {len(file_tasks)} tasks in {path}: {[x['locator'] for x in file_tasks]}")
        for y in file_tasks:
            y["file"] = path
        return file_tasks

    all_tasks:list[list[dict[str, Any]]] = parallel_runner(run_it, [(str(x),x) for x in rocq_files], None, jobs=jobs, progress=False)
    flat_tasks = list(itertools.chain.from_iterable(all_tasks))
    with open(output_file, 'w') as f:
        if output_file.suffix in [".yml", ".yaml"]:
            yaml.dump(flat_tasks, f)
        elif output_file.suffix == ".json":
            json.dump(flat_tasks, f)
        else:
            print(f"unknown file format! {output_file}")

def run_ns(args: Namespace, extra_args:list[str]|None=None) -> None:
    assert True if extra_args is None else len(extra_args) == 0
    return run(args.output, args.rocq_files, jobs=args.jobs)

def main() -> None:
    args = mk_parser().parse_args()
    run_ns(args)

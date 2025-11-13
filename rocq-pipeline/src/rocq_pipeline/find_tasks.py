import itertools
import json
import os
import re
import sys
from argparse import ArgumentParser, Namespace
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Union

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
def extract_tactics(s: Union[str, list[str]], allowed_prefixes: list[str]) -> tuple[list[str], list[str]]:
    """
    Extracts a list of Coq tactic prefixes from a string or list of strings,
    ensuring no duplicates in the output lists.

    Args:
        s: The input string (or list of strings) containing Coq tactics.
        allowed_prefixes: A list of tactic prefix strings to identify.

    Returns:
        A tuple containing two lists, both sorted and without duplicates:
        1. identified_tactics: A list of unique tactic prefixes found.
        2. leftovers: A list of unique processed chunks that did not match.
    """
    # Use sets to store results to automatically handle duplicates
    identified_tactics_set = set()
    leftovers_set = set()
    
    # Sort prefixes by length (longest first)
    sorted_prefixes = sorted(allowed_prefixes, key=len, reverse=True)

    def split_at_top_level(text: str, separator: str) -> list[str]:
        """
        Splits a string by a separator, but only at the top level
        (i.e., not inside parentheses or brackets).
        """
        parts = []
        balance_paren = 0
        balance_bracket = 0
        current_part_start = 0
        
        for i, char in enumerate(text):
            if char == '(':
                balance_paren += 1
            elif char == ')':
                balance_paren = max(0, balance_paren - 1)
            elif char == '[':
                balance_bracket += 1
            elif char == ']':
                balance_bracket = max(0, balance_bracket - 1)
            
            if char == separator and balance_paren == 0 and balance_bracket == 0:
                parts.append(text[current_part_start:i])
                current_part_start = i + 1
        
        parts.append(text[current_part_start:])
        return parts

    def process_chunk(chunk: str):
        """
        Recursively processes a chunk of the tactic string.
        """
        # Step 4: Clean chunk
        chunk = chunk.strip().strip(';.')
        chunk = chunk.strip()
        
        if not chunk:
            return

        # Step 3: Handle [ X1 | X2 | ... Xn ]
        if chunk.startswith('[') and chunk.endswith(']'):
            content = chunk[1:-1]
            parts = split_at_top_level(content, '|')
            for part in parts:
                process_chunk(part)
            return

        # Step 2: Handle X1; X2; ... Xn
        parts = split_at_top_level(chunk, ';')
        if len(parts) > 1:
            for part in parts:
                process_chunk(part)
            return

        # --- Base Case ---
        found_prefix = None
        for prefix in sorted_prefixes:
            if chunk == prefix:
                found_prefix = prefix
                break
            if chunk.startswith(prefix):
                next_char_index = len(prefix)
                if next_char_index < len(chunk) and chunk[next_char_index] in ' .(':
                    found_prefix = prefix
                    break
        
        # Step 7: Add to the appropriate set (duplicates are ignored)
        if found_prefix:
            identified_tactics_set.add(found_prefix)
        else:
            leftovers_set.add(chunk)

    # --- Main Function Logic ---
    
    if isinstance(s, str):
        string_list = [s]
    elif isinstance(s, list):
        string_list = s
    else:
        raise TypeError(f"Input 's' must be a string or a list of strings, but got {type(s)}")

    for input_string in string_list:
        if not isinstance(input_string, str):
            print(f"Warning: Skipping non-string item in list: {input_string}")
            continue
            
        s_to_process = input_string.strip()
        
        # Step 1: Handle 'by (X).' or 'by X.'
        if s_to_process.startswith('by ') and s_to_process.endswith('.'):
            content = s_to_process[3:-1].strip()
            if content.startswith('(') and content.endswith(')'):
                 s_to_process = content[1:-1].strip()
            else:
                 s_to_process = content
        
        process_chunk(s_to_process)
    
    # Convert sets to sorted lists for the final output
    return sorted(list(identified_tactics_set)), sorted(list(leftovers_set))

def my_tagger(task: ProofTask) -> list[str]:
    tags = ["admitted"] if task.admitted else []
    allowed_prefixes = ['verify_spec', 'go', 'ego', 'work', 'wp_for', 'wp_while', 'wp_do',
                         'rewrite', 'erewrite', 'rewrite_all', 'bind_ren', 'ren_hyp',
                         'apply', 'eapply', 'assumption', 'eassumption',
                         'case_decide', 'assert', 'simpl', 'Arith.arith_simpl',
                         'trivial', 'reflexivity', 'cbv', 'cbn', 'subst',
                         'clear', 'replace', 'specialize', 'generalize',
                         'intro', 'intros', 'destruct', 'inversion', 'exist', 'exfalso',
                         'lia', 'remember', 'symmetry', 'unfold', 'f_equal',
                         'constructor', 'econstructor', 'induction',
                         'intuition', 'iAssert', 'iExists', 'revert',
                         'left', 'right', 'Opaque', 'Transparent', 'admit' ]
    identified_tactics, leftovers = extract_tactics(task.proof_tactics, allowed_prefixes)
    result = tags + identified_tactics
    return result

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

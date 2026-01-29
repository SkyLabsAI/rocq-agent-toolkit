import json
import logging
import sys
from typing import Any

from argparse import Namespace

from rocq_doc_manager import RocqCursor, RocqDocManager

from rocq_pipeline.locator import FirstLemma

from pathlib import Path

# from rocq_pipeline.rocq_cursor import RocqCursor

logger = logging.getLogger(__name__)

def _find_summary(data):
    if not isinstance(data, dict):
        return None
    summary = data.get("summary")
    if isinstance(summary, dict):
        return summary
    results = data.get("results")
    if isinstance(results, dict):
        side_effects = results.get("side_effects")
        if isinstance(side_effects, dict):
            summary = side_effects.get("summary")
            if isinstance(summary, dict):
                return summary
    return None

def get_proofscript(data: dict[str, Any]) -> list[str] | None:
    summary = _find_summary(data)
    if isinstance(summary, dict):
        script = summary.get("proof_script")
        if isinstance(script, list):
            return script
        return None
    return None


def extract_nth_inferred_proofscript(
    file_path: str, n: int
) -> tuple[str, list[Any], str] | None:
    """
    Extracts the Nth line from a JSONL file and returns its proof script
    Looks under results->side_effects->summary when available.
    Assumes N is 1-based (i.e., N=1 is the first line).
    """
    target_index = n - 1  # Convert to 0-based index

    try:
        with open(file_path, encoding="utf-8") as f:
            line_count = sum(1 for _ in f)
            print(f"File: {file_path} has {line_count} lines.")
            f.seek(0)  # Reset file pointer to beginning
            for i, line in enumerate(f):
                if i == target_index:
                    try:
                        # Parse the line to ensure it's valid JSON
                        data = json.loads(line)
                        # Extract task_id and status
                        task_id = data.get("task_id", "Unknown")
                        status = data.get("status", "Unknown")
                        inferred_proof_script = get_proofscript(data)
                        print(f"Extracted line {i+1}. Status = {str(status)}, Task_id = {str(task_id)}")
                        if inferred_proof_script is None:
                            print(f"❌ Error: proof script found in line {n} is None.")
                            return None
                        if (
                            isinstance(task_id, str)
                            and isinstance(inferred_proof_script, list)
                            and isinstance(status, str)
                        ):
                            proof_status = (
                                "Qed" if status.lower() == "success" else "Fail"
                            )
                            print(f"Proof script from line {n}: {str(inferred_proof_script)}")
                            return task_id, inferred_proof_script, proof_status
                    except json.JSONDecodeError:
                        # print(f"❌ Error: Line {n} is not valid JSON.")
                        return None

        # If the loop finishes without returning, N is out of bounds
        print(f"❌ Error: File {file_path} contains fewer than {n} lines.")
        return None

    except FileNotFoundError:
        print(f"❌ Error: The file '{file_path}' was not found.")
        return None
    except Exception as e:
        print(f"❌ An unexpected error occurred: {e}")
        return None


def get_groundtruth_script(task_id: str, rocqfiles_path: str) -> tuple[list[str], str] | None:
    if task_id.count("#") != 1:
        raise ValueError("task_id must contain exactly one # separating two parts.")

    # Split the string once at the #
    rocq_file: str
    my_locator: str
    rocq_file, my_locator = task_id.split("#", 1)
    gt_file = Path(rocqfiles_path) / rocq_file
    print(f"Getting groundtruth for file: {str(gt_file)}, Locator: {my_locator}")
    # if my_locator.count(":") != 1:
    #    raise ValueError("Locator must contain exactly one colon separating two parts.")

    # Split the string once at the colon
    # theorem_or_lemma, theorem_name = my_locator.split(":", 1)
    # t = theorem_or_lemma.strip()
    # n = theorem_name.strip()
    # if t not in ["Theorem", "Lemma"]:
    #    raise ValueError("Locator must start with 'Theorem' or 'Lemma'.")


    #rdm = RocqDocManager([],str(gt_file),)
    with RocqDocManager([], str(gt_file), dune=True).sess(load_file=True) as rdm:
        rc: RocqCursor = rdm.cursor()

        first_lemma: FirstLemma | None = FirstLemma.parse(str(my_locator))
        if first_lemma is None:
            return None

        def find_lemma(text: str, kind: str) -> bool:
            parts = text.split(None, 1)  # splitting on whitespace
            if len(parts) != 2:
                return False  # raise ValueError("Input string must contain two parts separated by whitespace.")
            thm_or_lemma = parts[0]
            # The split handles leading space on x and space between x and y,
            # but y might still have trailing whitespace.
            lemmaname = parts[1].strip()
            res: bool = kind == "command" and f"{thm_or_lemma}:{lemmaname}" == str(
                first_lemma
            )  # is this the right comparison?
            return res

        rc.advance_to_first_match(find_lemma)
        suffix: list[RocqCursor.SuffixItem] = rc.doc_suffix()

        def extract_proof(
            suffixes: list[RocqCursor.SuffixItem],
        ) -> tuple[list[str], str] | None:
            prefix: list[str] = []

            for item in suffixes:
                txt = item.text

                if txt == "Qed":
                    return prefix, "Qed"
                elif txt in ["Admitted", "Abort"]:
                    return prefix, "Fail"
                prefix.append(txt)
            return None

        return extract_proof(suffix)


def extract_statistics(input_path: str, line_num: int, rocqfiles_path: str) -> dict[str, Any] | None:
    inferred = extract_nth_inferred_proofscript(input_path, line_num)
    if inferred is None:
        return None
    task_id, inf_script, inf_status = inferred

    groundtruth: tuple[list[str], str] | None
    groundtruth = get_groundtruth_script(task_id, rocqfiles_path)
    if groundtruth is None:
        return None
    gt_script: list[str]
    gt_status: str
    gt_script, gt_status = groundtruth
    res: dict[str, Any] = {
        "groundtruth_length": len(gt_script),
        "groundtruth_proof_status": gt_status,
        "inferred_length": len(inf_script),
        "inferred_proof_status": inf_status,
    }
    print(str(res))
    return res

def main() -> None:
    #args = mk_parser().parse_args()
    #run_ns(args)

    # Check if arguments are provided
    if len(sys.argv) != 4:
        print("Usage: uv run comparescript <file_path> <N> rocqfilesdir")
        print("Example: uv run comparescript data.jsonl 5 /home/workpace/bluerock/bhv")
        sys.exit(1)

    data_path = sys.argv[1]

    rocqfiles_path = sys.argv[3]

    try:
        line_num = int(sys.argv[2])
        if line_num < 1:
            print("Error: N must be 1 or greater.")
        else:
            extract_statistics(data_path, line_num, rocqfiles_path)
    except ValueError:
        print("Error: N must be an integer.")

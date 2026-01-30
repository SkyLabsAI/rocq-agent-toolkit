import json
import logging
import sys
from pathlib import Path
from typing import Any, Literal

from rocq_doc_manager import DuneUtil, RocqCursor, RocqDocManager

from rocq_pipeline.locator import FirstLemma

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
) -> tuple[str, list[str], Literal["Success", "Failure"]] | None:
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
                        inferred_proof_script: list[str] | None = get_proofscript(data)
                        print(
                            f"Line {i + 1}: Status = {str(status)}, Task_id = {str(task_id)}"
                        )
                        if inferred_proof_script is None:
                            print(f"❌ Error: proof script found in line {n} is None.")
                            return None
                        if isinstance(task_id, str) and isinstance(status, str):
                            status_literal: Literal["Success", "Failure"]
                            status_literal = (
                                "Success" if status.lower() == "success" else "Failure"
                            )
                            # print(
                            #    f"Inferred script: {str(inferred_proof_script)}, status = {status_literal}"
                            # )
                            return (task_id, inferred_proof_script, status_literal)
                        else:
                            return None
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


def get_groundtruth_script(
    task_id: str, rocqfiles_path: str
) -> tuple[list[str], Literal["Success", "Failure"]] | None:
    if task_id.count("#") != 1:
        raise ValueError("task_id must contain exactly one # separating two parts.")

    rocq_file: str
    my_locator: str
    rocq_file, my_locator = task_id.split("#", 1)
    gt_file = Path(rocqfiles_path) / rocq_file
    # print(
    #     f"Getting groundtruth for path {rocqfiles_path}, file: {rocq_file}, Locator: {my_locator}"
    # )

    args: list[str] = DuneUtil.rocq_args_for(gt_file)
    # print(f'args: {str(args)}')
    with RocqDocManager(args, str(gt_file), dune=True).sess(load_file=True) as rdm:
        rc: RocqCursor = rdm.cursor()

        first_lemma: FirstLemma | None = FirstLemma.parse(str(my_locator))
        if first_lemma is None:
            return None

        def find_lemma(text: str, kind: Literal["blanks", "command", "ghost"]) -> bool:
            parts = text.split(None, 1)  # splitting on whitespace
            if len(parts) != 2:
                return False  # raise ValueError("Input string must contain two parts separated by whitespace.")
            thm_or_lemma = parts[0]
            # The split handles leading space on x and space between x and y,
            # but y might still have trailing whitespace.
            statement = parts[1].strip()
            if thm_or_lemma in ["Theorem", "Lemma"]:
                lemmaname = (
                    statement.split(":", 1)[0] if ":" in statement else statement
                )
                searchstring = (f"{thm_or_lemma}:{lemmaname}").strip()
                # print(f"Comparing lemma: kind={str(kind)}, searchstring={searchstring} with first_lemma={str(first_lemma)}")
                res: bool = (
                    kind == "command" and searchstring == (str(first_lemma)).strip()
                )
            else:
                res = False
            return res

        found = rc.goto_first_match(find_lemma)
        if not found:
            print(f"❌ Error: Could not find lemma {str(first_lemma)} in file.")
            return None
        index: int = rc.cursor_index()
        script_start: None | RocqCursor.Err[RocqCursor.CommandError | None] = rc.go_to(
            index + 3
        )  # step to beginning of proof script
        if script_start is not None:
            print("❌ Error: Could not navigate to proof script start.")
            return None
        suffix: list[RocqCursor.SuffixItem] = rc.doc_suffix()
        # num_suffixes = len(suffix)
        # print(f"Number of suffix items after locating lemma: {num_suffixes}")
        gt_script: list[str] = []
        status: Literal["Success", "Failure"] = "Failure"
        i = 0
        while i < len(suffix):
            item = suffix[i]
            txt = item.text
            if not txt.isspace():
                gt_script.append(txt)
                if txt == "Qed.":
                    status = "Success"
                if txt in ["Qed.", "Admitted.", "Abort."]:
                    break
            i += 1
        # print(f"Groundtruth script: {str(gt_script)}")

        return (gt_script, status)


def extract_statistics(
    input_path: str, line_num: int, rocqfiles_path: str
) -> dict[str, Any] | None:
    inferred: tuple[str, list[str], Literal["Success", "Failure"]] | None = (
        extract_nth_inferred_proofscript(input_path, line_num)
    )
    if inferred is None:
        return None
    task_id, inf_script, inf_status = inferred
    i_script = " ".join(inf_script)

    groundtruth: tuple[list[str], Literal["Success", "Failure"]] | None
    groundtruth = get_groundtruth_script(task_id, rocqfiles_path)
    if groundtruth is None:
        return None
    gt_script: list[str]
    gt_status: Literal["Success", "Failure"]
    gt_script, gt_status = groundtruth
    g_script = " ".join(gt_script)
    res: dict[str, Any] = {
        "groundtruth_length": len(gt_script),
        "groundtruth_script": g_script,
        "groundtruth_proof_status": gt_status,
        "inferred_length": len(inf_script),
        "inferred_script": i_script,
        "inferred_proof_status": inf_status,
    }
    print(str(res))
    return res


def main() -> None:
    # args = mk_parser().parse_args()
    # run_ns(args)

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

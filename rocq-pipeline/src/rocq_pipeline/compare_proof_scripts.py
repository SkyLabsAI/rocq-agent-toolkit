import json
import logging
import os
import sys
from pathlib import Path
from typing import Any, Literal

from rocq_doc_manager import DuneUtil, RocqCursor, RocqDocManager

from rocq_pipeline.find_tasks import scan_proof
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
            # line_count = sum(1 for _ in f)
            # print(f"File: {file_path} has {line_count} lines.")
            f.seek(0)  # Reset file pointer to beginning
            lines = f.readlines()

        for i, line in enumerate(lines):
            if i == target_index:
                try:
                    # Parse the line to ensure it's valid JSON
                    data = json.loads(line)
                    # Extract task_id and status
                    task_id = data.get("task_id", "Unknown")
                    status = data.get("status", "Unknown")
                    inferred_proof_script: list[str] | None = get_proofscript(data)
                    # print(f"Line {i + 1}: Status = {str(status)}, Task_id = {str(task_id)}")

                    if inferred_proof_script is None:
                        logger.error(
                            f"❌ Error: proof script found in line {n} is None."
                        )
                        return None
                    if isinstance(task_id, str) and isinstance(status, str):
                        status_literal: Literal["Success", "Failure"]
                        status_literal = (
                            "Success" if status.lower() == "success" else "Failure"
                        )
                        return (task_id, inferred_proof_script, status_literal)
                    else:
                        return None
                except json.JSONDecodeError:
                    logger.error(f"❌ Error: Line {n} is not valid JSON.")
                    return None

        # If the loop finishes without returning, N is out of bounds
        logger.error(f"❌ Error: File {file_path} contains fewer than {n} lines.")
        return None

    except FileNotFoundError:
        logger.error(f"❌ Error: The file '{file_path}' was not found.")
        return None
    except Exception as e:
        logger.error(f"❌ An unexpected error occurred: {e}")
        return None


def find_lemma(lemma: str):
    def inner(txt: str, kind: Literal["blanks", "command", "ghost"]) -> bool:
        parts = txt.split(None, 1)
        if len(parts) != 2:
            return False
        thm_or_lemma = parts[0]
        # The split handles leading space on x and space between x and y,
        # but y might still have trailing whitespace.
        statement = parts[1].strip()
        if thm_or_lemma in ["Theorem", "Lemma"]:
            lemmaname = statement.split(":", 1)[0] if ":" in statement else statement
            searchstring = (f"{thm_or_lemma}:{lemmaname}").strip()
            res: bool = kind == "command" and searchstring == lemma.strip()
        else:
            res = False
        return res

    return inner


def get_groundtruth_lemma(
    task_id: str, rocqfiles_path: str
) -> tuple[FirstLemma, Path] | None:
    if task_id.count("#") != 1:
        raise ValueError("task_id must contain exactly one # separating two parts.")

    rocq_file, my_locator = task_id.split("#", 1)

    first_lemma: FirstLemma | None = FirstLemma.parse(my_locator)
    if first_lemma is None:
        return None

    gt_file = Path(rocqfiles_path) / rocq_file
    if not os.path.exists(gt_file):
        logger.error(f"❌ Error: groundtruth file not found: {gt_file}")
        return None
    return first_lemma, gt_file


def get_groundtruth_script_via_RDM(
    task_id: str, rocqfiles_path: str
) -> tuple[list[str], Literal["Success", "Failure"]] | None:
    gt = get_groundtruth_lemma(task_id, rocqfiles_path)
    if gt is None:
        return None
    first_lemma, gt_file = gt

    args: list[str] = DuneUtil.rocq_args_for(gt_file)
    with RocqDocManager(args, str(gt_file), dune=True).sess(load_file=True) as rdm:
        rc: RocqCursor = rdm.cursor()

        found = rc.goto_first_match(find_lemma(str(first_lemma)))
        if not found:
            logger.error(f"❌ Error: Could not find lemma {str(first_lemma)} in file.")
            return None
        suffix: list[RocqCursor.SuffixItem] = rc.doc_suffix()
        if len(suffix) == 0:
            logger.error("❌ Error: Suffix after locating lemma is empty.")
            return None
        prooftask = scan_proof(
            suffix[1:]
        )  # skip the first item (the lemma statement itself)

        gt_script = prooftask.proof_tactics
        status: Literal["Success", "Failure"] = (
            "Success" if prooftask.final == "qed" else "Failure"
        )

        return (gt_script, status)


def get_groundtruth_script_from_vfile(
    task_id: str, rocqfiles_path: str
) -> tuple[list[str], Literal["Success", "Failure"]] | None:
    gt = get_groundtruth_lemma(task_id, rocqfiles_path)
    if gt is None:
        return None
    first_lemma, gt_file = gt

    with open(gt_file, encoding="utf-8") as f:
        lines = f.readlines()
    found = False
    index = 0
    for i, line in enumerate(lines):
        if find_lemma(str(first_lemma))(line, "command"):
            found = True
            index = i + 1
            break
    if not found:
        logger.error(f"❌ Error: Could not find locator {str(first_lemma)} in file.")
        return None

    script: list[str] = []
    while index < len(lines):
        line = f"{lines[index].strip()} "  # Add trailing space here so we can split on '. ' below
        if (
            line.startswith("Qed.")
            or line.startswith("Admitted.")
            or line.startswith("Abort.")
        ):
            status: Literal["Success", "Failure"] = (
                "Success" if line.startswith("Qed.") else "Failure"
            )
            return (script, status)
        if not line.startswith("Proof") and not line.startswith("cpp_sound"):
            segments = line.split(". ")
            cleaned_segments = [
                f"{segment.strip()}." for segment in segments if segment.strip()
            ]
            script += cleaned_segments
        index += 1
    return None


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

    gt_v = get_groundtruth_script_from_vfile(task_id, rocqfiles_path)
    if gt_v is None:
        return None
    v_status: Literal["Success", "Failure"]
    v_script, v_status = gt_v

    groundtruth = get_groundtruth_script_via_RDM(task_id, rocqfiles_path)
    if groundtruth is None:
        return None
    gt_status: Literal["Success", "Failure"]
    gt_script, gt_status = groundtruth
    g_script = " ".join(gt_script)
    res: dict[str, Any] = {
        "v_length": len(v_script),
        "v_script": " ".join(v_script),
        "v_proof_status": v_status,
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
            logger.error("Error: N must be 1 or greater.")
        else:
            extract_statistics(data_path, line_num, rocqfiles_path)
    except ValueError:
        logger.error("Error: N must be an integer.")

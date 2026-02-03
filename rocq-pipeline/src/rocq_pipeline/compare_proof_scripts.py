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


def parse_inference_line(
    line: str, n: int
) -> tuple[str, list[str], Literal["Success", "Failure"]] | None:
    try:
        data = json.loads(line)

        task_id = data.get("task_id", "Unknown")
        status = data.get("status", "Unknown")
        inferred_proof_script: list[str] | None = get_proofscript(data)
        # print(f"Line {i + 1}: Status = {str(status)}, Task_id = {str(task_id)}")

        if inferred_proof_script is None:
            logger.error(f"❌ Error: proof script found in line {n} is None.")
            return None
        if isinstance(task_id, str) and isinstance(status, str):
            status_literal: Literal["Success", "Failure"]
            status_literal = "Success" if status.lower() == "success" else "Failure"
            return (task_id, inferred_proof_script, status_literal)
        else:
            return None
    except json.JSONDecodeError:
        logger.error(f"❌ Error: Line {n} is not valid JSON.")
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
            f.seek(0)  # Reset file pointer to beginning
            lines = f.readlines()

        for i, line in enumerate(lines):
            if i == target_index:
                return parse_inference_line(line, i)

        # If the loop finishes without returning, N is out of bounds
        logger.error(f"❌ Error: File {file_path} contains fewer than {n} lines.")
        return None

    except FileNotFoundError:
        logger.error(f"❌ Error: The file '{file_path}' was not found.")
        return None
    except Exception as e:
        logger.error(f"❌ An unexpected error occurred: {e}")
        return None


def extract_inferred_proofscripts(
    file_path: str,
    k: int | None = None,  # none :extract all lines, k: inly line k-1
) -> list[tuple[str, list[str], Literal["Success", "Failure"]]] | None:
    """
    Extracts all lines from a JSONL file and returns their proof scripts
    Looks under results->side_effects->summary when available.
    """

    try:
        with open(file_path, encoding="utf-8") as f:
            if k is None:
                line_count = sum(1 for _ in f)
                print(f"File {file_path} has {line_count} lines.")
            f.seek(0)  # Reset file pointer to beginning
            lines = f.readlines()

        result: list[tuple[str, list[str], Literal["Success", "Failure"]]] = []
        for i, line in enumerate(lines):
            if k is None or i == k - 1:
                line_result = parse_inference_line(line, i)
                if line_result is not None:
                    result.append(line_result)
        return result

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

            # using startswith allow us to fine lemmas such as 'Theorem compiler_export_ptr_ok `{!nova.AbsPred arch}:'
            res: bool = kind == "command" and searchstring.startswith(lemma.strip())
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
            logger.error(
                f"❌ Error: Could not find lemma {str(first_lemma)} in file {str(gt_file)}."
            )
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
        logger.error(
            f"❌ Error: Could not find locator {str(first_lemma)} in file {str(gt_file)}."
        )
        return None

    script: list[str] = []

    # procede until we find 'Proof', 'Admitted', or 'Abort'
    while index < len(lines):
        line = f"{lines[index].strip()}"
        if (
            line.startswith("Proof")
            or line.startswith("Admitted")
            or line.startswith("Abort")
        ):
            break
        index += 1

    if index >= len(lines):
        logger.error(
            f"❌ Error: Could not find the proof start for {str(first_lemma)} in file {str(gt_file)}."
        )
        return None

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


def treat_line(
    inferred: tuple[str, list[str], Literal["Success", "Failure"]],
    rocqfiles_path: str,
    use_rdm: bool = False,
) -> tuple[str, dict[str, tuple[list[str], Literal["Success", "Failure"]] | None]]:
    task_id, inf_script, inf_status = inferred

    gtruth_v = get_groundtruth_script_from_vfile(task_id, rocqfiles_path)

    gtruth_rdm = (
        get_groundtruth_script_via_RDM(task_id, rocqfiles_path) if use_rdm else None
    )

    entry = {
        "inferred": (inf_script, inf_status),
        "ground_v": gtruth_v,
        "ground_rdm": gtruth_rdm,
    }
    res = (task_id, entry)
    return res


def extract_statistics(
    input_path: str,
    rocqfiles_path: str,
    line_num: int | None = None,
    use_rdm: bool = False,
) -> (
    None
    | list[
        tuple[str, dict[str, tuple[list[str], Literal["Success", "Failure"]] | None]]
    ]
):
    inferred = extract_inferred_proofscripts(input_path, line_num)
    if inferred is None:
        return None
    return [treat_line(inf, rocqfiles_path, use_rdm) for inf in inferred]

def print_entries(entries: list[tuple[str, dict[str, tuple[list[str], Literal["Success", "Failure"]] | None]]]) -> None:
    i = 0
    j = 0
    v_list: list[float] = []
    rdm_list: list[float] = []
    for task_id, entry in entries:
        print(f"Task ID: {task_id}")
        inf = entry.get("inferred")
        ground_v = entry.get("ground_v")
        ground_rdm = entry.get("ground_rdm")
        print(f"  inferred: {inf}")
        print(f"  ground_v: {ground_v}")
        print(f"  ground_rdm: {ground_rdm}")
        if inf is not None and inf[1] == "Success":
            if ground_v is not None and ground_v[1] == "Success":
                print(f"  inf / ground_v = {len(inf[0])} / {len(ground_v[0])}")
                i = i + 1
                v_list.append((float(len(inf[0])) / float(len(ground_v[0])) if len(ground_v[0]) > 0 else 0))
            if ground_rdm is not None and ground_rdm[1] == "Success":
                print(f"  inf / ground_rdm = {len(inf[0])} / {len(ground_rdm[0])}")
                j = j + 1
                rdm_list.append((float(len(inf[0])) / float(len(ground_rdm[0])) if len(ground_rdm[0]) > 0 else 0))
    if i > 0:
        avg_v = sum(v_list) / float(i)
        print(f"Average ratio inferred proof size / ground_v proof size over {i} successful proofs: {avg_v}. Note: use of ; and comments may affect the result.")
    if j > 0:
        avg_rdm = sum(rdm_list) / float(j)
        print(f"Average ratio inferred proof size / ground_rdm proof size over {j} successful proofs: {avg_rdm}. Note: use of ; may affect the result.")

def main() -> None:
    # args = mk_parser().parse_args()
    # run_ns(args)

    # Check if arguments are provided
    if len(sys.argv) != 5:
        print("Usage: uv run comparescript <file_path> <N> rocqfilesdir use_rdm")
        print(
            "Example: uv run comparescript data.jsonl 5 /home/workpace/bluerock/bhv True"
        )
        sys.exit(1)

    data_path = sys.argv[1]

    rocqfiles_path = sys.argv[3]

    use_rdm: bool = sys.argv[4].lower() == "true"

    try:
        arg2 = sys.argv[2]
        line_num: int | None
        if arg2.lower() == "all":
            line_num = None
        else:
            line_num = int(arg2)
            if line_num < 1:
                logger.error("Error: N must be 1 or greater.")
                return
        res = extract_statistics(data_path, rocqfiles_path, line_num, use_rdm)
        if res is not None:
            print_entries(res)
        else:
            print("No data extracted.")
    except ValueError:
        logger.error("Error: N must be an integer or 'all'.")

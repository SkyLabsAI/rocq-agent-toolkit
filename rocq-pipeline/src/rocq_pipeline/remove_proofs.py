import asyncio
import re
import sys
from collections.abc import Sequence
from pathlib import Path
from typing import Literal

from rocq_doc_manager import rc_sess
from rocq_doc_manager.rocq_doc_manager_api import PrefixItem, SuffixItem

_SUCCEED_OR_FAIL = re.compile(r"^(Succeed|Fail)\s.*")


def strip_proofs_from_doc_items(suffix: Sequence[SuffixItem | PrefixItem]) -> list[str]:
    processed: list[str] = []
    in_proof: tuple[bool, str, int] | None = None
    for i, item in enumerate(suffix):
        # print(f"i={i}, in_proof={in_proof}\nitem={item}")
        if item.data is None:
            if in_proof is None or (not in_proof[0] and item.kind == "blanks"):
                processed.append(item.text)
        elif _SUCCEED_OR_FAIL.match(item.text):
            # HACK: This works around a classification bug in the RDM
            if in_proof is None:
                processed.append(item.text)
        elif item.data.kind == "Abort":
            assert in_proof is not None
            started, proof_cmd, proof_start = in_proof
            processed.extend(f"{proof_cmd} Abort.")
            in_proof = None

        elif item.data.kind == "EndProof":
            assert in_proof is not None
            started, proof_cmd, proof_start = in_proof
            if item.text.startswith(("Qed", "Admitted")):
                processed.extend(f"{proof_cmd} Admitted.")
            else:
                processed.extend("".join(t.text for t in suffix[proof_start : i + 1]))
            in_proof = None

        elif item.data.kind == "ExactProof":
            processed.append("Proof. Admitted.")
        elif item.data.kind == "StartTheoremProof":
            processed.append(item.text)
            assert in_proof is None
            in_proof = (False, "Proof.", i + 1)
        elif item.data.kind == "Proof":
            if in_proof is not None and in_proof[0]:
                # Support for `Next Obligation. Proof.`
                continue
            in_proof = (True, item.text, i)
        elif item.text.startswith("Next Obligation"):
            in_proof = (True, item.text, i)
        elif item.data.kind == "Definition":
            # this is probably a definition
            processed.append(item.text)
            if ":=" not in item.text:
                in_proof = (False, "", i + 1)
        elif in_proof is None:
            processed.append(item.text)
    return processed


async def strip_proofs(file: Path, *, output: Literal["-"] | Path) -> None:
    async with rc_sess(file, rocq_args="dune") as rc:
        suffix = await rc.doc_suffix()
        result = strip_proofs_from_doc_items(suffix)
    output_str = "".join(result)
    if output == "-":
        print(output_str)
    else:
        with open(file, "w") as f:
            f.write("".join(result))


def main() -> None:
    output: Path | Literal["-"]
    match sys.argv[1]:
        case "-":
            output = "-"
        case "-i":
            output = Path(sys.argv[2])
        case _:
            output = Path(sys.argv[1])
    asyncio.run(strip_proofs(Path(sys.argv[2]), output=output))

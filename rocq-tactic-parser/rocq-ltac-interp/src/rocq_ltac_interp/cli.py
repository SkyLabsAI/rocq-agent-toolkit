import argparse
import asyncio
import json
import sys
from pathlib import Path

from rocq_doc_manager import rc_sess
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_doc_manager.locator import Locator, LocatorParser
from rocq_dune_util import rocq_args_for
from rocq_dune_util.rocq_dune_util import DuneRocqPlugin

from rocq_ltac_interp.tacinterp import interp


async def amain(file: Path, locator: Locator) -> int:
    plugin = DuneRocqPlugin(
        opam_pkg="rocq-tactic-parser", entry_points=["theories/explain.v"]
    )
    rocq_args = rocq_args_for(file, plugins=[plugin])
    async with rc_sess(file, rocq_args=rocq_args) as rc:
        assert isinstance(
            await rc.run_command("Require Import skylabs_ai.tactic_parser.explain."),
            rdm_api.CommandData,
        )
        assert await locator.go_to(rc)

        suffix = await rc.doc_suffix()
        for i, tactic in enumerate([t for t in suffix if t.kind == "command"]):
            if tactic.data and tactic.data.kind in ["EndProof"]:
                break
            tac_str = tactic.text
            print(f"{i}/ {tac_str}")
            explanation = await rc.query(f"Explain {tac_str}")
            if isinstance(explanation, rdm_api.Err):
                print("query failed!")
                raise Exception("Oops")
            explanation = json.loads(explanation.feedback_messages[0].text)
            await interp(rc, explanation, goals=(0, 1))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Trace a proof")

    # Accept any number of file paths
    # 'nargs='+' means 1 or more files are required.
    # Use '*' if you want to allow running with zero files.
    parser.add_argument("file", type=Path, help="Input file")
    parser.add_argument("locator", help="The locator", type=LocatorParser.parse)

    args = parser.parse_args()

    return asyncio.run(amain(args.file, args.locator))


if __name__ == "__main__":
    sys.exit(main())

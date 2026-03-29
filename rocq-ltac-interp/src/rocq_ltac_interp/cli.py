import argparse
import asyncio
import sys
from pathlib import Path

from rocq_doc_manager import rc_sess
from rocq_doc_manager.cursor.protocol import RocqCursor
from rocq_doc_manager.locator import Locator, LocatorParser
from rocq_doc_manager.rocq_doc_manager_api import ProofState
from rocq_dune_util import rocq_args_for

from . import tacinterp as tacinterp
from .tacinterp import (
    RunCommandResult,
    interp_tactic_str,
)


async def amain(
    file: Path, locator: Locator, *, trace: bool = False, trace_atom: bool = False
) -> int:
    if trace_atom:

        async def run_atom(
            rc: RocqCursor,
            goal: int,
            tac: str,
            *,
            pre: ProofState,
            trace: int | None = None,
        ) -> RunCommandResult:
            return await tacinterp.run_atom(
                rc, goal, tac, pre=pre, trace=2 if trace is None else trace
            )

    else:
        run_atom = tacinterp.run_atom

    rocq_args = rocq_args_for(file, plugins=[tacinterp.PLUGIN])
    async with rc_sess(file, rocq_args=rocq_args) as rc:
        await tacinterp.load(rc)
        assert await locator.go_to(rc)

        suffix = await rc.doc_suffix()
        for i, tactic in enumerate([t for t in suffix if t.kind == "command"]):
            if tactic.data and tactic.data.kind in ["EndProof"]:
                break

            print(f"{i}/ {tactic.text}")
            await interp_tactic_str(
                rc, tactic.text, trace=0 if trace else None, run_atom=run_atom
            )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Trace a proof")

    # Accept any number of file paths
    # 'nargs='+' means 1 or more files are required.
    # Use '*' if you want to allow running with zero files.
    parser.add_argument("file", type=Path, help="Input file")
    parser.add_argument("locator", help="The locator", type=LocatorParser.parse)
    parser.add_argument(
        "-t",
        dest="trace",
        action="store_true",
        default=False,
        help="Trace all operations",
    )
    parser.add_argument(
        "-1",
        dest="trace_atom",
        action="store_true",
        default=False,
        help="Trace atomic operations",
    )

    args = parser.parse_args()

    return asyncio.run(
        amain(args.file, args.locator, trace=args.trace, trace_atom=args.trace_atom)
    )


if __name__ == "__main__":
    sys.exit(main())

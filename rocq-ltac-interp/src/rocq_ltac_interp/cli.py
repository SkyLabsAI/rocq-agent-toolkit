import argparse
import asyncio
import sys
from pathlib import Path

from rocq_doc_manager import rc_sess
from rocq_doc_manager.cursor.protocol import RocqCursor
from rocq_doc_manager.locator import Locator, LocatorParser
from rocq_dune_util import rocq_args_for

from rocq_ltac_interp.tacinterp import (
    PLUGIN,
    RunCommandResult,
    interp_rec,
    load,
    parse_tactic,
    run_tac,
)


async def amain(
    file: Path, locator: Locator, *, trace: bool = False, trace_atom: bool = False
) -> int:
    if trace_atom:

        async def run_atom(
            rc: RocqCursor, goal: int, tac: str, *, trace: int | None = None
        ) -> RunCommandResult:
            return await run_tac(rc, goal, tac, trace=2 if trace is None else trace)

    else:
        run_atom = run_tac

    rocq_args = rocq_args_for(file, plugins=[PLUGIN])
    async with rc_sess(file, rocq_args=rocq_args) as rc:
        await load(rc)
        assert await locator.go_to(rc)

        suffix = await rc.doc_suffix()
        for i, tactic in enumerate([t for t in suffix if t.kind == "command"]):
            if tactic.data and tactic.data.kind in ["EndProof"]:
                break
            explanation = await parse_tactic(rc, tactic.text)
            print(f"{i}/ {tactic.text}")

            await interp_rec(
                rc, explanation, trace=0 if trace else None, run_atom=run_atom
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
        "-t", dest="trace", action="store_true", default=False, help="Trace all output"
    )
    parser.add_argument(
        "-1",
        dest="trace_atom",
        action="store_true",
        default=False,
        help="Trace atommic operations only",
    )

    args = parser.parse_args()

    return asyncio.run(
        amain(args.file, args.locator, trace=args.trace, trace_atom=args.trace_atom)
    )


if __name__ == "__main__":
    sys.exit(main())

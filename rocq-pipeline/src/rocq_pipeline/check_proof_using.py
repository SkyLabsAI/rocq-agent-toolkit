import argparse
import asyncio
import re
import sys
import traceback
from collections.abc import Sequence
from pathlib import Path

from pydantic import BaseModel, Field
from rocq_doc_manager import RocqCursor, rc_sess
from rocq_doc_manager.rocq_doc_manager_api import (
    CommandData,
    Err,
    PrefixItem,
    SuffixItem,
)

from rocq_pipeline.util import ProgressCallback, parallel_runner

_SUCCEED_OR_FAIL = re.compile(r"^(Succeed|Fail)\s.*")


class FileOffset(BaseModel):
    line: int = Field(description="line number (0 base)", ge=0)
    col: int = Field(description="column number (0 base)", ge=0)
    offset: int = Field(description="full file offset (0 base)", ge=0)


async def cursor_offset(rc: RocqCursor) -> FileOffset:
    """Compute the offset of a RocqCursor.

    TODO: This function should probably be replaced with something else"""
    prefix = await rc.doc_prefix()
    contents = "".join(x.text for x in prefix if x.kind != "ghost")
    if contents == "":
        return FileOffset(line=0, col=0, offset=0)
    offset = len(contents)
    lines = contents.splitlines()
    line = max(0, len(lines))
    if contents[-1] == "\n":
        col = 0
    else:
        col = len(lines[-1])
    return FileOffset(line=line, col=col, offset=offset)


async def process(
    rc: RocqCursor,
    suffix: Sequence[SuffixItem | PrefixItem],
    *,
    progress: ProgressCallback | None = None,
    trace: bool = False,
) -> list[tuple[str, FileOffset, str, str]]:
    errors: list[tuple[str, FileOffset, str, str]] = []
    processed: list[str] = []
    modules: list[str] = []
    sections: list[str] = []
    # in_proof tracks the following:
    # - whether this is an obligation (if so, it might not complete the definition)
    # - whether this was explicitly started (we do not revert back to implicitly
    #   created proofs)
    # - the commands for opening the proof, e.g. `Next Obligation. Proof.`
    # - the cursor_index that starts the proof
    # - the FileOffset that starts the proof
    in_proof: tuple[bool, bool, str, int, FileOffset] | None = None

    async def revert_to_top_of_proof(rc: RocqCursor) -> None:
        nonlocal in_proof
        assert in_proof is not None
        _, one_more, _, to, _ = in_proof
        await rc.go_to(to)
        if one_more:
            assert not isinstance(await rc.run_step(), Err)

    async def end_sections(rc: RocqCursor) -> None:
        nonlocal sections
        for s in reversed(sections):
            result = await rc.run_command(f"End {s}.")
            if isinstance(result, Err):
                print(f"Popping section {s} resulted in err: {result}.")
                print(f"Sections = {sections}")

    step = 1.0 / len(suffix)

    for i, item in enumerate(suffix):
        result = await rc.run_step()
        assert not isinstance(result, Err)
        if progress:
            progress.status(percent=i * step)
        if trace:
            print(f"i={i}, in_proof={in_proof}\nitem={item}")
        if item.data is None:
            if in_proof is None or (not in_proof[0] and item.kind == "blanks"):
                processed.append(item.text)
        elif _SUCCEED_OR_FAIL.match(item.text):
            # HACK: This works around a classification bug in the RDM
            if in_proof is None:
                processed.append(item.text)
        elif item.data.kind == "DefineModule":
            if not item.data.attrs["defn"]:
                assert not sections
                modules.append(item.data.attrs["id"])
        elif item.data.kind in ["DeclareModuleType"]:
            if not item.data.attrs["defn"]:
                assert not sections
                modules.append(item.data.attrs["id"])
        elif item.data.kind == "BeginSection":
            sections.append(item.data.attrs["id"])
        elif item.data.kind == "EndSegment":
            if sections:
                top = sections.pop()
                assert top == item.data.attrs["id"]
            elif modules:
                top = modules.pop()
                assert top == item.data.attrs["id"]
            else:
                raise Exception(f"Unmatched End. {item.text}")

        elif item.data.kind == "Abort":
            assert in_proof is not None
            _is_obligation, _started, proof_cmd, proof_start, _ = in_proof
            processed.extend(f"{proof_cmd} Abort.")
            in_proof = None

        elif item.data.kind == "EndProof":
            assert in_proof is not None
            is_obligation, started, proof_cmd, proof_start, offset = in_proof
            if item.text.startswith(("Qed", "Admitted")):
                processed.extend(f"{proof_cmd} Admitted.")
                if sections:
                    assert isinstance(result, CommandData)
                    if is_obligation:
                        # If we are in an obligation, then we can not
                        # close sections if there are additional obligations
                        obligations = await rc.query("Obligations.")
                        assert not isinstance(obligations, Err)
                        if obligations.feedback_messages:
                            in_proof = None
                            continue

                    symbol = result.globrefs_diff.added_constants[0]
                    if symbol.startswith("sections."):
                        symbol = symbol[len("sections.") :]
                    # print(f"Going to check '{symbol}'")
                    basename = symbol.rsplit(".")[-1]

                    async def extract_type(rc: RocqCursor, symbol: str) -> str:
                        index = await rc.cursor_index()
                        await rc.run_command("Set Printing All.")
                        about = await rc.query(f"About {symbol}.")
                        await rc.revert_before(erase=True, index=index)
                        assert isinstance(about, CommandData)
                        for m in about.feedback_messages:
                            if m.level == "notice":
                                # The message contains `name : type\n\n...`
                                line = m.text.split("\n\n")[0]
                                # remove the name
                                return line.split(":", 1)[1]
                        raise Exception(
                            f"Failed to parse type from {about.feedback_messages}"
                        )

                    async with (await rc.clone(materialize=True)).sess() as rc_base:
                        await end_sections(rc_base)
                        finished = await extract_type(rc_base, basename)
                        await revert_to_top_of_proof(rc_base)
                        await rc_base.run_command("Admitted.")
                        await end_sections(rc_base)
                        admitted = await extract_type(rc_base, basename)
                        if finished != admitted:
                            errors.append(
                                (
                                    symbol,
                                    offset,
                                    finished.replace("\n", " "),
                                    admitted.replace("\n", " "),
                                )
                            )
                        # else:
                        #     print(f"OK {symbol}")
                        # print(f"As occurs:\n{finished}\nAdmitted:\n{admitted}")

            else:
                processed.extend("".join(t.text for t in suffix[proof_start : i + 1]))
            in_proof = None

        elif item.data.kind == "ExactProof":
            processed.append("Proof. Admitted.")
        elif item.data.kind == "StartTheoremProof":
            processed.append(item.text)
            assert in_proof is None
            in_proof = (
                False,
                False,
                "Proof.",
                await rc.cursor_index(),
                await cursor_offset(rc),
            )
        elif item.data.kind == "Proof":
            assert in_proof is not None
            if in_proof[1]:
                # Support for `Next Obligation. Proof.`
                continue
            else:
                in_proof = (
                    in_proof[0],
                    True,
                    item.text,
                    await rc.cursor_index(),
                    in_proof[4],
                )

        elif item.text.startswith("Next Obligation"):
            in_proof = (
                True,
                True,
                item.text,
                await rc.cursor_index(),
                await cursor_offset(rc),
            )
        elif item.data.kind in ["Definition", "Instance"]:
            # this is probably a definition
            processed.append(item.text)
            assert result is not None
            if result.proof_state is not None:
                in_proof = (
                    False,
                    False,
                    "",
                    await rc.cursor_index(),
                    await cursor_offset(rc),
                )
        elif in_proof is None:
            processed.append(item.text)
    return errors


async def check_deps(
    file: Path, *, progress: ProgressCallback | None = None, trace: bool = False
) -> list[tuple[str, FileOffset, str, str]]:
    async with rc_sess(file, rocq_args="dune") as rc:
        suffix = await rc.doc_suffix()
        return await process(rc, suffix, progress=progress, trace=trace)


def parallel_main(files: list[Path], *, progress: bool = True, jobs: int = 1) -> None:
    async def run(file: Path, progress: ProgressCallback) -> list[str]:
        results = await check_deps(file, progress=progress)
        return [
            f"{file}:{symbol}:'{finished}' vs '{admitted}'"
            for symbol, offset, finished, admitted in results
        ]

    def succeeded(out: list[str]) -> bool:
        print(f"STATUS {out}")
        for err in out:
            print(err, flush=True)
        return len(out) == 0

    parallel_runner(
        run, [(str(p), p) for p in files], jobs=jobs, progress=True, succeeded=succeeded
    )


async def amain(files: list[Path]) -> None:
    for p in files:
        try:
            results = await check_deps(p)  # , trace=True)
            if results:
                print(f"❌ {p}", flush=True)
                for symbol, _offset, finished, admitted in results:
                    print(f"> {symbol}:'{finished}' vs '{admitted}'", flush=True)
            else:
                print(f"✅ {p}", flush=True)
        except Exception as err:
            print(f"⁉️ {p}: {err}")
            traceback.print_exc()


def main(args: list[str] | None = None) -> None:
    if args is None:
        args = sys.argv[1:]
    assert args is not None
    parser = argparse.ArgumentParser(description="Check `Proof using` annotations.")
    parser.add_argument("files", type=Path, nargs="+", help="List of input file paths")
    # parser.add_argument("-i", action="store_true", help="Write results in-place")

    parser.add_argument(
        "-j",
        metavar="N",
        dest="jobs",
        type=int,
        default=1,
        help="number of parallel jobs (default: 1)",
    )

    parser.add_argument(
        "-o",
        metavar="filename",
        dest="output",
        type=Path,
        default="-",
        help="number of parallel jobs (default: 1)",
    )

    arguments = parser.parse_args(args)

    if arguments.jobs > 1:
        parallel_main(arguments.files, jobs=arguments.jobs)
    else:
        asyncio.run(amain(arguments.files))

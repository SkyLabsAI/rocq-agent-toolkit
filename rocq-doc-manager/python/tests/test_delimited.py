from pathlib import Path

import pytest
from rocq_doc_manager import rc_sess
from rocq_doc_manager import rocq_doc_manager_api as rdm_api
from rocq_doc_manager.cursor import DelimitedRocqCursor


def starts_module(item: rdm_api.SuffixItem, name: str) -> bool:
    if item.data is None:
        return False
    if item.data.kind != "DefineModule":
        return False
    if item.data.attrs["id"] != name:
        return False
    return True


def ends_module(item: rdm_api.SuffixItem, name: str) -> bool:
    if item.data is None:
        return False
    if item.data.kind != "EndSegment":
        return False
    if item.data.attrs["id"] != name:
        return False
    return True


def locate_module(suffix: list[rdm_api.SuffixItem], name: str) -> tuple[int, int]:
    start = next(i for i, item in enumerate(suffix) if starts_module(item, name))
    end = next(i for i, item in enumerate(suffix) if ends_module(item, name))
    return (start, end)


@pytest.mark.asyncio
async def test_delimited() -> None:
    p = Path(__file__).parent / "test_delimited.v"
    async with rc_sess(str(p), load_file=True) as rc:
        suffix = await rc.doc_suffix()
        assert len(suffix) == 26
        (bar_start, bar_end) = locate_module(suffix, "Bar")
        assert bar_start == 8
        assert bar_end == 22
        dc = await DelimitedRocqCursor.make(rc, start=bar_start + 1, end=bar_end)
        assert isinstance(dc, DelimitedRocqCursor)
        # Checking that the prefix / index / suffix make sense.
        assert await dc.cursor_index() == 0
        assert len(await dc.doc_prefix()) == 0
        assert len(await dc.doc_suffix()) == 13
        assert (await dc.doc_suffix())[12].kind == "blanks"
        assert (await dc.doc_suffix())[12].text == " (* END *)\n"
        # Checking that we can process the whole suffix, but not beyond.
        for _ in range(13):
            await dc.run_step()
        failed = False
        try:
            await dc.run_step()
        except Exception:
            failed = True
        assert failed
        # Checking that we can insert at the start.
        await dc.go_to(0)
        await dc.run_step()
        res = await dc._insert_command("About bool.")
        assert isinstance(res, rdm_api.CommandData)
        await dc.insert_blanks("\n  ")
        # Checking that we can insert at the end.
        await dc.go_to(15)
        assert len(await dc.doc_suffix()) == 0
        res = await dc._insert_command("About bool.")
        assert isinstance(res, rdm_api.CommandData)
        await dc.insert_blanks("\n  ")
        assert len(await dc.doc_prefix()) == 17


@pytest.mark.asyncio
async def test_delimited_empty_start() -> None:
    p = Path(__file__).parent / "test_delimited.v"
    async with rc_sess(str(p), load_file=True) as rc:
        dc = await DelimitedRocqCursor.make(rc, start=0, end=0)
        assert isinstance(dc, DelimitedRocqCursor)
        assert len(await dc.doc_prefix()) == 0
        assert len(await dc.doc_suffix()) == 0
        res = await dc._insert_command("About bool.")
        assert isinstance(res, rdm_api.CommandData)
        assert len(await dc.doc_prefix()) == 1
        assert len(await dc.doc_suffix()) == 0


@pytest.mark.asyncio
async def test_delimited_empty_end() -> None:
    p = Path(__file__).parent / "test_delimited.v"
    async with rc_sess(str(p), load_file=True) as rc:
        suffix = await rc.doc_suffix()
        assert len(suffix) == 26
        dc = await DelimitedRocqCursor.make(rc, start=26, end=26)
        assert isinstance(dc, DelimitedRocqCursor)
        assert len(await dc.doc_prefix()) == 0
        assert len(await dc.doc_suffix()) == 0
        res = await dc._insert_command("About bool.")
        assert isinstance(res, rdm_api.CommandData)
        assert len(await dc.doc_prefix()) == 1
        assert len(await dc.doc_suffix()) == 0


@pytest.mark.asyncio
async def test_delimited_full() -> None:
    p = Path(__file__).parent / "test_delimited.v"
    async with rc_sess(str(p), load_file=True) as rc:
        len_suffix = len(await rc.doc_suffix())
        dc = await DelimitedRocqCursor.make(rc)
        assert isinstance(dc, DelimitedRocqCursor)
        assert await dc.cursor_index() == await rc.cursor_index()
        assert len(await dc.doc_prefix()) == 0
        assert len(await dc.doc_suffix()) == len_suffix
        res = await dc._insert_command("About bool.")
        assert isinstance(res, rdm_api.CommandData)
        await dc.insert_blanks("\n")
        assert len(await dc.doc_prefix()) == 2
        assert len(await dc.doc_suffix()) == len_suffix


@pytest.mark.asyncio
async def test_delimited_count() -> None:
    p = Path(__file__).parent / "test_delimited.v"
    async with rc_sess(str(p), load_file=True) as rc:
        await rc.run_step()
        await rc.run_step()
        # Check failure if count is too large.
        failed = False
        try:
            dc = await DelimitedRocqCursor.make(rc, count=25)
        except Exception:
            failed = True
        assert failed
        # Check of if taking everything.
        failed = False
        try:
            dc = await DelimitedRocqCursor.make(rc, count=24)
        except Exception:
            failed = True
        assert not failed
        # Checking prefix / suffix length
        dc = await DelimitedRocqCursor.make(rc, count=2)
        assert isinstance(dc, DelimitedRocqCursor)
        assert len(await dc.doc_prefix()) == 0
        assert len(await dc.doc_suffix()) == 2

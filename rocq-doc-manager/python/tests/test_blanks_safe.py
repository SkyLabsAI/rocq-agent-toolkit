from pathlib import Path

import pytest
from rocq_doc_manager import RocqCursor, rc_sess
from rocq_doc_manager.rocq_doc_manager_api import CommandData


@pytest.mark.asyncio
async def test_no_blanks() -> None:
    async def split(rc: RocqCursor, text: str) -> list[str]:
        sentences = await rc.split_sentences(text)
        assert isinstance(sentences, list)
        return [s.text for s in sentences]

    async with rc_sess(Path(__file__).parent / "locator_test.v") as rc:
        assert await split(rc, "idtac. idtac.") == ["idtac.", " ", "idtac."]

        assert isinstance(await rc.run_step(), CommandData)
        # At this point we should be immediately after a command

        assert await split(rc, "idtac. idtac.") == ["idtac.", " ", "idtac."]
        assert await split(rc, "\nidtac. idtac.") == ["\n", "idtac.", " ", "idtac."]
        assert await split(rc, "(*oops*)idtac.") == ["(*oops*)", "idtac."]


@pytest.mark.asyncio
async def test_invariant() -> None:
    async def check_invariant(rc: RocqCursor, ls: list[str]) -> None:
        prefix = await rc.doc_prefix()
        assert [p.text for p in prefix] == ["(**)", "Lemma foo : True."] + ls
        assert [p.text for p in prefix] == ["(**)", "Lemma foo : True."] + ls

    async with rc_sess(Path(__file__).parent / "locator_test.v") as rc:
        await rc.insert_blanks("(**)")
        assert isinstance(await rc.run_step(), CommandData)
        # At this point we should be immediately after a command

        async with (await rc.clone()).ctx() as rc1:
            await rc1.insert_blanks(" ")
            await check_invariant(rc1, [" "])

        async with (await rc.clone()).ctx() as rc2:
            await rc2.insert_blanks("(* *) ")
            await check_invariant(rc2, ["\n", "(* *) "])

        async with (await rc.clone()).ctx() as rc3:
            assert isinstance(await rc3.insert_command("About nat."), CommandData)
            await check_invariant(rc3, ["\n", "About nat.", "\n"])


@pytest.mark.asyncio
async def test_blanks_revert() -> None:
    async with rc_sess(Path(__file__).parent / "locator_test.v") as rc:
        try:
            await rc.insert_command("About nat.", blanks="bad")
            failed = False
        except Exception:
            failed = True
        assert failed
        assert len(await rc.doc_prefix()) == 0

        assert isinstance(await rc.insert_command("About nat."), CommandData)
        assert len(await rc.doc_prefix()) == 2

        assert isinstance(
            await rc.insert_command("About nat.", blanks=None), CommandData
        )
        assert len(await rc.doc_prefix()) == 3

        await rc.insert_blanks("(* needs extra whitespace before *)")
        assert len(await rc.doc_prefix()) == 5

        assert isinstance(
            await rc.insert_command("About nat.", blanks=None), CommandData
        )
        assert len(await rc.doc_prefix()) == 6
        assert isinstance(await rc.insert_command("About nat."), CommandData)
        assert len(await rc.doc_prefix()) == 9

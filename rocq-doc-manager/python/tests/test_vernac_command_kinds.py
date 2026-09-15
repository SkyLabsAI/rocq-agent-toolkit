"""Keep typed command metadata compatible with native command tags."""

import os

import pytest
from pydantic import ValidationError
from rocq_doc_manager import create
from rocq_doc_manager import rocq_doc_manager_api as api

@pytest.mark.parametrize("kind", ["Abbreviation", "DeclareMLModule", "SchemeAll"])
def test_supported_native_kinds_in_document_items(kind: str) -> None:
    data = {"kind": kind}
    assert api.VernacData.model_validate(data).kind == kind
    suffix = api.SuffixItem.model_validate(
        {"text": "", "kind": "command", "data": data}
    )
    prefix = api.PrefixItem.model_validate(
        {"text": "", "offset": 0, "kind": "command", "data": data}
    )
    assert suffix.data is not None and suffix.data.kind == kind
    assert prefix.data is not None and prefix.data.kind == kind


def test_unknown_native_kind_is_still_rejected() -> None:
    with pytest.raises(ValidationError):
        api.VernacData.model_validate({"kind": "NotARealVernacCommand"})


@pytest.mark.asyncio(loop_scope="class")
class TestNativeAbbreviation:
    async def test_split_abbreviation(self) -> None:
        # A transient document: no .v file, dependency build, or proof execution.
        manager = await create(
            "schema_only.v",
            dune=os.environ.get("RDM_USE_DUNE", "True") == "True",
        )
        try:
            sentences = await manager.cursor().split_sentences("Notation short_nat := nat.")
            assert isinstance(sentences, list)
            commands = [item for item in sentences if item.kind == "command"]
            assert len(commands) == 1
            assert commands[0].data is not None
            assert commands[0].data.kind == "Abbreviation"
        finally:
            await manager.quit()

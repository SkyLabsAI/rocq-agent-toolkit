import pytest
from rocq_doc_manager import AsyncRocqDocManager
from rocq_doc_manager import rocq_doc_manager_api as rdm_api

from .util import RDM_Tests


@pytest.mark.asyncio(loop_scope="class")
class Test_RDM_advance_to_first_match(RDM_Tests):
    def _no_match(self, text: str, kind: str) -> bool:
        return False

    def _match_any_Theorem(self, text: str, kind: str) -> bool:
        return kind == "command" and text.startswith("Theorem")

    @pytest.mark.parametrize("steps", list(range(0, 18)))
    async def test_advance_to_first_match_none(
        self,
        steps: int,
        loaded_shared_rdm: AsyncRocqDocManager,
    ) -> None:
        async with RDM_Tests.starting_from(loaded_shared_rdm.cursor(), idx=0) as rc:
            assert not isinstance(
                await rc.advance_to(steps),
                rdm_api.Err,
            )
            assert not await rc.goto_first_match(
                self._no_match,
            )

    @pytest.mark.parametrize("steps", list(range(0, 9)))
    @pytest.mark.parametrize("step_over_match", [True, False])
    async def test_advance_to_first_match_some(
        self,
        steps: int,
        step_over_match: bool,
        loaded_shared_rdm: AsyncRocqDocManager,
    ) -> None:
        async with RDM_Tests.starting_from(loaded_shared_rdm.cursor(), idx=0) as rc:
            assert not isinstance(
                await rc.advance_to(steps),
                rdm_api.Err,
            )
            assert await rc.goto_first_match(
                self._match_any_Theorem,
                step_over_match=step_over_match,
            )

            theorem_item: rdm_api.PrefixItem | rdm_api.SuffixItem
            if step_over_match:
                theorem_item = (await rc.doc_prefix())[-1]
            else:
                theorem_item = (await rc.doc_suffix())[0]
            assert theorem_item.text.startswith("Theorem")

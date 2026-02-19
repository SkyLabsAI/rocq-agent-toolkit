import pytest
from rocq_doc_manager import AsyncRocqDocManager
from rocq_doc_manager import rocq_doc_manager_api as rdm_api

from .util import RDM_Tests


@pytest.mark.asyncio(loop_scope="class")
class Test_RDM_Tests(RDM_Tests):
    @staticmethod
    async def test_fixtures_ok(
        transient_shared_rdm: AsyncRocqDocManager,
        transient_rdm: AsyncRocqDocManager,
        loadable_rdm: AsyncRocqDocManager,
    ) -> None:
        assert not isinstance(
            await transient_shared_rdm.cursor().cursor_index(),
            rdm_api.Err,
        )
        assert not isinstance(
            await transient_rdm.cursor().cursor_index(),
            rdm_api.Err,
        )
        async with loadable_rdm.sess() as rdm:
            assert not isinstance(
                await rdm.cursor().cursor_index(),
                rdm_api.Err,
            )

from hypothesis import given, settings, strategies as st
import pytest

from rocq_doc_manager import RocqDocManager
from .util import RDM_Tests


class Test_RDM_macros(RDM_Tests):
    @given(
        n=st.integers(min_value=0, max_value=50),
        m=st.integers(min_value=0, max_value=50),
    )
    @settings(deadline=None, max_examples=50)
    @pytest.mark.slow
    def test_Compute_addition(
            self,
            n: int,
            m: int
    ) -> None:
        rdm = self.mk_rdm()
        with self.assert_doc_unchanged(rdm):
            compute_reply = rdm.Compute(f"{n}+{m}", rollback=True)
            assert not isinstance(compute_reply, RocqDocManager.Err)
            assert compute_reply == (str(n+m), "nat")

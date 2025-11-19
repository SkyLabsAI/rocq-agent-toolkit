from hypothesis import given, settings, strategies as st
import pytest

from rocq_doc_manager import RocqDocManager
from .util import RDM_Tests


class Test_RDM_macros(RDM_Tests):
    @given(
        n=st.integers(min_value=0, max_value=100),
        m=st.integers(min_value=0, max_value=100),
    )
    @settings(deadline=None)
    def test_Compute_addition(
            self,
            transient_shared_rdm: RocqDocManager,
            n: int,
            m: int,
    ) -> None:
        with self.assert_doc_unchanged(transient_shared_rdm):
            with transient_shared_rdm.ctx():
                compute_reply = transient_shared_rdm.Compute(
                    f"{n}+{m}",
                )
                assert not isinstance(compute_reply, RocqDocManager.Err)
                assert compute_reply == (str(n+m), "nat")

    def test_fresh_ident_repeated(
            self,
            transient_rdm: RocqDocManager,
    ) -> None:
        with self.assert_doc_unchanged(transient_rdm):
            with transient_rdm.ctx():
                nm: str = "x"
                val: int | str = 0
                for _ in range(20):
                    defn = f"Definition {nm} := {val}."
                    assert not isinstance(
                        transient_rdm.insert_command(defn),
                        RocqDocManager.Err,
                    ), f"Bad Definition: {defn}"
                    fresh_ident_reply = transient_rdm.fresh_ident(nm)
                    assert not isinstance(
                        fresh_ident_reply,
                        RocqDocManager.Err
                    )
                    val = nm
                    nm = fresh_ident_reply

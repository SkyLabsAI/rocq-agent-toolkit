import pytest
from hypothesis import given, settings
from hypothesis import strategies as st
from rocq_doc_manager import RocqDocManager

from .util import RDM_Tests


class Test_RDM_advance_to_first_match(RDM_Tests):
    def _no_match(self, text: str, kind: str) -> bool:
        return False

    def _match_any_Theorem(self, text: str, kind: str) -> bool:
        return kind == "command" and text.startswith("Theorem")

    @given(
        steps=st.integers(
            min_value=0,
            max_value=RDM_Tests.TEST_DOT_V_DOC_LEN,
        )
    )
    def test_advance_to_first_match_none(
        self,
        steps: int,
        loaded_shared_rdm: RocqDocManager,
    ) -> None:
        with RDM_Tests.starting_from(loaded_shared_rdm, idx=0) as rdm:
            assert not isinstance(
                rdm.advance_to(steps),
                RocqDocManager.Err,
            )
            assert not rdm.advance_to_first_match(
                self._no_match,
            )

    @given(
        steps=st.integers(
            min_value=0,
            max_value=RDM_Tests.TEST_DOT_V_NO_THEOREM_PREFIX_LEN,
        )
    )
    @settings(deadline=None)
    @pytest.mark.parametrize("step_over_match", [True, False])
    def test_advance_to_first_match_some(
        self,
        steps: int,
        step_over_match: bool,
        loaded_shared_rdm: RocqDocManager,
    ) -> None:
        with RDM_Tests.starting_from(loaded_shared_rdm, idx=0) as rdm:
            assert not isinstance(
                rdm.advance_to(steps),
                RocqDocManager.Err,
            )
            assert rdm.advance_to_first_match(
                self._match_any_Theorem,
                step_over_match=step_over_match,
            )

            theorem_item: RocqDocManager.PrefixItem | RocqDocManager.SuffixItem
            if step_over_match:
                theorem_item = rdm.doc_prefix()[-1]
            else:
                theorem_item = rdm.doc_suffix()[0]
            assert theorem_item.text.startswith("Theorem")

import pytest

from rocq_doc_manager import RocqDocManager
from .util import RDM_Tests


class Test_API(RDM_Tests):
    @pytest.mark.parametrize('rdm_fixture', ['loadable_rdm', 'transient_rdm'])
    def test_non_existant(
            self,
            rdm_fixture: str,
            request: pytest.FixtureRequest,
    ) -> None:
        rdm = request.getfixturevalue(rdm_fixture)
        result = rdm.raw_request("non-existant", [])
        assert isinstance(result, RocqDocManager.Err)
        assert result == RocqDocManager.Err("Method non-existant not found.", data=None)

    def test_load_file(self, loadable_rdm: RocqDocManager) -> None:
        result = loadable_rdm.raw_request("load_file", [])
        assert isinstance(result, RocqDocManager.Resp)
        assert result == RocqDocManager.Resp(None)

        result = loadable_rdm.raw_request("doc_suffix", [])
        assert isinstance(result, RocqDocManager.Resp)
        assert result == RocqDocManager.Resp([{'kind': "command", 'text': "Require Import Stdlib.ZArith.BinInt."}, {'kind': 'blanks', 'text': '\n\n'}, {'kind': 'command', 'text': 'About nil.'}, {'kind': 'blanks', 'text': '\n    '}, {'kind': 'command', 'text': 'Definition junk :=\n\n\nnat.'}, {'kind': 'blanks', 'text': '\n'}, {'kind': 'command', 'text': 'Check 12 < 42 <= 100.'}, {'kind': 'blanks', 'text': '\n\n\n'}, {'kind': 'command', 'text': 'Theorem test : forall x : nat, x = x.'}, {'kind': 'blanks', 'text': '\n'}, {'kind': 'command', 'text': 'Proof.'}, {'kind': 'blanks', 'text': '\n  '}, {'kind': 'command', 'text': 'intro x.'}, {'kind': 'blanks', 'text': '\n  '}, {'kind': 'command', 'text': 'reflexivity.'}, {'kind': 'blanks', 'text': '\n'}, {'kind': 'command', 'text': 'Qed.'}])

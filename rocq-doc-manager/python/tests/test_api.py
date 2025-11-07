from rocq_doc_manager import RocqDocManager


def make() -> RocqDocManager:
    return RocqDocManager([], "./tests/test.v")

def test_non_existant() -> None:
    result = make().request("non-existant", [])
    assert isinstance(result, RocqDocManager.Err)
    assert result == RocqDocManager.Err("Method non-existant not found.", data=None)

def test_load_file() -> None:
    dm = make()
    result = dm.request("load_file", [])
    assert isinstance(result, RocqDocManager.Resp)
    assert result == RocqDocManager.Resp(None)

    result = dm.request("doc_suffix", [])
    assert isinstance(result, RocqDocManager.Resp)
    assert result == RocqDocManager.Resp([{'kind': "command", 'text': "Require Import Stdlib.ZArith.BinInt."}, {'kind': 'blanks', 'text': '\n\n'}, {'kind': 'command', 'text': 'About nil.'}, {'kind': 'blanks', 'text': '\n    '}, {'kind': 'command', 'text': 'Definition junk :=\n\n\nnat.'}, {'kind': 'blanks', 'text': '\n'}, {'kind': 'command', 'text': 'Check 12 < 42 <= 100.'}, {'kind': 'blanks', 'text': '\n\n\n'}, {'kind': 'command', 'text': 'Theorem test : forall x : nat, x = x.'}, {'kind': 'blanks', 'text': '\n'}, {'kind': 'command', 'text': 'Proof.'}, {'kind': 'blanks', 'text': '\n  '}, {'kind': 'command', 'text': 'intro x.'}, {'kind': 'blanks', 'text': '\n  '}, {'kind': 'command', 'text': 'reflexivity.'}, {'kind': 'blanks', 'text': '\n'}, {'kind': 'command', 'text': 'Qed.'}])

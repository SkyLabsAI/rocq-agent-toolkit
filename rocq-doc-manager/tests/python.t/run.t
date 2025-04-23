  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ python3 -m venv _pyenv
  $ source _pyenv/bin/activate
  $ pip install --quiet "$DUNE_SOURCEROOT/_build/install/default/lib/rocq-doc-manager/python" 2>/dev/null

  $ python test.py
  RocqDocManager.Err(message='Method non-existant not found.', data=None)
  RocqDocManager.Resp(result=None)
  RocqDocManager.Resp(result=[{'kind': 'command', 'text': 'Require Import Stdlib.ZArith.BinInt.'}, {'kind': 'blanks', 'text': '\n\n'}, {'kind': 'command', 'text': 'About nil.'}, {'kind': 'blanks', 'text': '\n    '}, {'kind': 'command', 'text': 'Definition junk :=\n\n\nnat.'}, {'kind': 'blanks', 'text': '\n'}, {'kind': 'command', 'text': 'Check 12 < 42 <= 100.'}, {'kind': 'blanks', 'text': '\n\n\n'}, {'kind': 'command', 'text': 'Theorem test : forall x : nat, x = x.'}, {'kind': 'blanks', 'text': '\n'}, {'kind': 'command', 'text': 'Proof.'}, {'kind': 'blanks', 'text': '\n  '}, {'kind': 'command', 'text': 'intro x.'}, {'kind': 'blanks', 'text': '\n  '}, {'kind': 'command', 'text': 'reflexivity.'}, {'kind': 'blanks', 'text': '\n'}, {'kind': 'command', 'text': 'Qed.'}])

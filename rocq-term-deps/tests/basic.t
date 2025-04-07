  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v <<EOF
  > Require Import skylabs_ai.tools.term_deps.plugin.
  > Fail DepsOf nat.
  > DepsOf Nat.add.
  > Definition weird (x y : nat) := x + (y * 2) + 1.
  > DepsOf weird.
  > EOF

  $ coqc test.v
  Constants:
  Inductives:
  - Corelib.Init.Datatypes.nat
  
  Constants:
  - Corelib.Init.Nat.mul
  - Corelib.Init.Nat.add
  Inductives:
  - Corelib.Init.Datatypes.nat
  

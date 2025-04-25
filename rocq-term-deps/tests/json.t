  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v <<EOF
  > Require Import skylabs_ai.tools.term_deps.plugin.
  > Fail DepsOf nat.
  > DepsOfJSON Nat.add.
  > Definition weird (x y : nat) := x + (y * 2) + 1.
  > DepsOfJSON weird.
  > EOF

  $ coqc test.v
  {
    "name": "Corelib.Init.Nat.add",
    "kind": "Def",
    "inductive_deps": [ "Corelib.Init.Datatypes.nat" ],
    "constant_deps": []
  }
  {
    "name": "test.weird",
    "kind": "Def",
    "inductive_deps": [ "Corelib.Init.Datatypes.nat" ],
    "constant_deps": [ "Corelib.Init.Nat.mul", "Corelib.Init.Nat.add" ]
  }

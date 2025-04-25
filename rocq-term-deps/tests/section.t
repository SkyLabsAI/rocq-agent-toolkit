  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v <<EOF
  > Require Import skylabs_ai.tools.term_deps.plugin.
  > Section junk.
  >   Context (k m n : nat).
  >   Definition f := k + m + n.
  >   DepsOfJSON f.
  > End junk.
  > DepsOfJSON f.
  > EOF

  $ coqc test.v
  {
    "name": "test.f",
    "kind": "Def",
    "inductive_deps": [ "Corelib.Init.Datatypes.nat" ],
    "constant_deps": [ "Corelib.Init.Nat.add" ]
  }
  {
    "name": "test.f",
    "kind": "Def",
    "inductive_deps": [ "Corelib.Init.Datatypes.nat" ],
    "constant_deps": [ "Corelib.Init.Nat.add" ]
  }

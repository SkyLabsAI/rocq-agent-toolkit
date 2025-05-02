  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v <<EOF
  > Require Import skylabs_ai.tools.term_deps.plugin.
  > Section junk.
  >   Context (k m n : nat).
  >   Definition f := k + m + n.
  >   DepsOfJSON f.
  >   DepsOfJSON test.dir.test.junk.f.
  >   Definition g := f + k.
  >   DepsOfJSON test.dir.test.junk.g.
  > End junk.
  > DepsOfJSON f.
  > DepsOfJSON test.dir.test.f.
  > DepsOfJSON test.dir.test.g.
  > EOF

  $ coqc -Q . test.dir test.v
  {
    "name": "test.dir.test.f",
    "kind": "Def",
    "inductive_deps": [ "Corelib.Init.Datatypes.nat" ],
    "constant_deps": [ "Corelib.Init.Nat.add" ]
  }
  {
    "name": "test.dir.test.f",
    "kind": "Def",
    "inductive_deps": [ "Corelib.Init.Datatypes.nat" ],
    "constant_deps": [ "Corelib.Init.Nat.add" ]
  }
  {
    "name": "test.dir.test.g",
    "kind": "Def",
    "inductive_deps": [ "Corelib.Init.Datatypes.nat" ],
    "constant_deps": [ "Corelib.Init.Nat.add", "test.dir.test.f" ]
  }
  {
    "name": "test.dir.test.f",
    "kind": "Def",
    "inductive_deps": [ "Corelib.Init.Datatypes.nat" ],
    "constant_deps": [ "Corelib.Init.Nat.add" ]
  }
  {
    "name": "test.dir.test.f",
    "kind": "Def",
    "inductive_deps": [ "Corelib.Init.Datatypes.nat" ],
    "constant_deps": [ "Corelib.Init.Nat.add" ]
  }
  {
    "name": "test.dir.test.g",
    "kind": "Def",
    "inductive_deps": [ "Corelib.Init.Datatypes.nat" ],
    "constant_deps": [ "Corelib.Init.Nat.add", "test.dir.test.f" ]
  }

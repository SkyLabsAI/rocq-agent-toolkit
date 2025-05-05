  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ cat > test.v <<EOF
  > Variant i := Test.
  > Definition junk m n := m + n * n.
  > Theorem test : forall x : nat, x = x.
  > Proof.
  >   intro x.
  >   reflexivity.
  > Qed.
  > Module Type mt.
  >   Definition d := 1 + 1.
  > End mt.
  > Section junk.
  >   Context (i j k : nat).
  >   Definition f := i + j + k.
  > End junk.
  > EOF

  $ rocq-get-deps -Q . test.dir test.v
  [
    { "name": "test.dir.test.i", "kind": "Inductive" },
    {
      "name": "test.dir.test.junk",
      "kind": "Def",
      "inductive_deps": [ "Corelib.Init.Datatypes.nat" ],
      "constant_deps": [ "Corelib.Init.Nat.mul", "Corelib.Init.Nat.add" ]
    },
    { "name": "test.dir.test.test", "kind": "OpaqueDef" },
    {
      "name": "test.dir.test.f",
      "kind": "Def",
      "inductive_deps": [ "Corelib.Init.Datatypes.nat" ],
      "constant_deps": [ "Corelib.Init.Nat.add" ]
    }
  ]

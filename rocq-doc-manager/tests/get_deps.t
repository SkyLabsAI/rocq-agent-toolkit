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
  > 
  > #[program]
  > Definition p : nat * nat := (_, _).
  > Next Obligation. exact 42. Defined.
  > Next Obligation. exact 73. Defined.
  > EOF

  $ rocq-get-deps -Q . test.dir test.v
  [
    { "name": "test.dir.test.i", "kind": "Inductive", "off": 0, "len": 18 },
    {
      "name": "test.dir.test.junk",
      "kind": "Def",
      "inductive_deps": [ "Corelib.Init.Datatypes.nat" ],
      "constant_deps": [ "Corelib.Init.Nat.mul", "Corelib.Init.Nat.add" ],
      "off": 19,
      "len": 33
    },
    { "name": "test.dir.test.test", "kind": "OpaqueDef", "off": 124, "len": 4 },
    {
      "name": "test.dir.test.f",
      "kind": "Def",
      "inductive_deps": [ "Corelib.Init.Datatypes.nat" ],
      "constant_deps": [ "Corelib.Init.Nat.add" ],
      "off": 219,
      "len": 26
    },
    {
      "name": "test.dir.test.p_obligation_1",
      "kind": "Def",
      "inductive_deps": [ "Corelib.Init.Datatypes.nat" ],
      "constant_deps": [],
      "off": 331,
      "len": 8
    },
    {
      "name": "test.dir.test.p",
      "kind": "Def",
      "inductive_deps": [
        "Corelib.Init.Datatypes.prod", "Corelib.Init.Datatypes.nat"
      ],
      "constant_deps": [
        "test.dir.test.p_obligation_2", "test.dir.test.p_obligation_1"
      ],
      "off": 367,
      "len": 8
    },
    {
      "name": "test.dir.test.p_obligation_2",
      "kind": "Def",
      "inductive_deps": [ "Corelib.Init.Datatypes.nat" ],
      "constant_deps": [],
      "off": 367,
      "len": 8
    }
  ]

  $ cat > test.v <<EOF
  > Definition junk m n := m +
  > EOF

  $ rocq-get-deps -Q . test.dir test.v
  File "test.v", line 2, characters 0-1:
  Error: Syntax error: [term] expected after '+' (in [term]).
  [1]

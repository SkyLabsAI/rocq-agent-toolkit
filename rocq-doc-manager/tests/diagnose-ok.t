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

  $ rocq-diagnose test.v -- -Q . test.dir
  { "status": "success" }

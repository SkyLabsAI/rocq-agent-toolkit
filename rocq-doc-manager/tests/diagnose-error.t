  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ cat > test.v <<EOF
  > Variant i := Test.
  > Definition junk m n := m + n * n.
  > Theorem test : forall x : nat, x = x.
  > Proof.
  >   intro x.
  >   (*reflexivity.*)
  > Qed.
  > EOF

  $ rocq-diagnose test.v -- -Q . test.dir
  {
    "status": "error",
    "message": " (in proof test): Attempt to save an incomplete proof\n(there are remaining open goals).",
    "loc": {
      "fname": [ "ToplevelInput" ],
      "line_nb": 1,
      "bol_pos": 0,
      "line_nb_last": 1,
      "bol_pos_last": 0,
      "bp": 128,
      "ep": 132
    },
    "goals": "1 goal\n  \n  x : nat\n  ============================\n  x = x"
  }

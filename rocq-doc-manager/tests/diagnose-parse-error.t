  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ cat > test.v <<EOF
  > Variant i := Test.
  > Definition junk m n := m + n * n.
  > Theorem test : forall x : nat, x = x.
  > Proof.
  >   intro x
  > EOF

  $ rocq-diagnose -Q . test.dir test.v
  {
    "status": "error",
    "message": "Syntax error: [ltac_use_default] expected after [tactic] (in [tactic_command]).",
    "loc": {
      "fname": [ "InFile", { "dirpath": null, "file": "test.v" } ],
      "line_nb": 6,
      "bol_pos": 108,
      "line_nb_last": 6,
      "bol_pos_last": 108,
      "bp": 108,
      "ep": 109
    }
  }

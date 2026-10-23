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
      "fname": [ "InFile", { "dirpath": null, "file": "test.v" } ],
      "line_nb": 7,
      "bol_pos": 128,
      "line_nb_last": 7,
      "bol_pos_last": 128,
      "bp": 128,
      "ep": 132
    },
    "proof_state": {
      "focused_goals": [ "\nx : nat\n============================\nx = x" ]
    }
  }

Regression test for issue #399: locations from commands parsed separately retain
source-file line metadata as well as byte offsets.

  $ cat > lineno.v <<EOF
  > Lemma a : True.
  > Proof. exact I. Qed.
  > EOF
  $ printf '\n' >> lineno.v
  $ cat >> lineno.v <<EOF
  > Lemma b : 1 = 2.
  > Proof. reflexivity. Qed.
  > EOF

  $ rocq-diagnose lineno.v -- -Q . test.dir
  {
    "status": "error",
    "message": "Unable to unify \"2\" with \"1\".",
    "loc": {
      "fname": [ "InFile", { "dirpath": null, "file": "lineno.v" } ],
      "line_nb": 5,
      "bol_pos": 55,
      "line_nb_last": 5,
      "bol_pos_last": 55,
      "bp": 62,
      "ep": 73
    },
    "proof_state": {
      "focused_goals": [ "\n============================\n1 = 2" ]
    }
  }

Location advancement through blanks is delegated to Rocq's lexer, including
when multibyte UTF-8 characters occur before the next command.

  $ cat > unicode.v <<'EOF'
  > Lemma unicode : 1 = 2.
  > (* λ *)
  > Proof. reflexivity. Qed.
  > EOF

  $ rocq-diagnose unicode.v -- -Q . test.dir
  {
    "status": "error",
    "message": "Unable to unify \"2\" with \"1\".",
    "loc": {
      "fname": [ "InFile", { "dirpath": null, "file": "unicode.v" } ],
      "line_nb": 3,
      "bol_pos": 32,
      "line_nb_last": 3,
      "bol_pos_last": 32,
      "bp": 39,
      "ep": 50
    },
    "proof_state": {
      "focused_goals": [ "\n============================\n1 = 2" ]
    }
  }

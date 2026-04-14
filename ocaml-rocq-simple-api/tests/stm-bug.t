  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ cat > commands.txt <<EOF
  > run 0 "Goal 0 = 0."
  > run 0 "Require Import Corelib.Init.Prelude."
  > run 0 "Proof (eq_refl _)."
  > EOF

  $ cat commands.txt | rocq-simple-api.toplevel
  [0] 1 > run 0 "Goal 0 = 0."
  {
    "synterp_ast": { "controls": [], "tag": "Definition", "pure": true },
    "proof_state": {
      "focused_goals": [ "\n============================\n0 = 0" ]
    }
  }
  [0] 2 > run 0 "Require Import Corelib.Init.Prelude."
  {
    "synterp_ast": { "controls": [], "tag": "Require", "pure": false },
    "proof_state": {
      "focused_goals": [ "\n============================\n0 = 0" ]
    }
  }
  [0] 4 > run 0 "Proof (eq_refl _)."
  Error: while processing the command.
  Anomaly "Non-qed command classified incorrectly"
  Please report at http://rocq-prover.org/bugs/.
  {
    "error_loc": {
      "fname": [ "ToplevelInput" ],
      "line_nb": 1,
      "bol_pos": 0,
      "line_nb_last": 1,
      "bol_pos_last": 0,
      "bp": 0,
      "ep": 18
    },
    "feedback_messages": [
      {
        "level": "error",
        "text": "Anomaly \"Non-qed command classified incorrectly\"\nPlease report at http://rocq-prover.org/bugs/."
      }
    ]
  }
  [0] 4 > [EOF]

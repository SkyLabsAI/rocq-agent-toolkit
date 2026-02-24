  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ cat > commands.txt <<EOF
  > run 0 "Definition test := nat. XXX"
  > run 42 "Definition test := nat. "
  > run 0 "Goal 0 = 0."
  > run 0 "Proof.   "
  > run 0 "Proof."
  > run 127 "- reflexivity."
  > run 0 "- "
  > run 0 " -"
  > run 0 "-"
  > run 0 "reflexivity."
  > run 0 "Qed."
  > run 0 "Goal 0 = 0."
  > run 0 "Proof."
  > run 0 "1:"
  > run 0 "1: reflexivity."
  > run 0 "1:{ "
  > run 0 "1:{"
  > run 0 "reflexivity."
  > run 246 "} "
  > run 0 " }"
  > run 0 "}"
  > run 0 "Qed."
  > run 0 "  Locate nat."
  > EOF

  $ cat commands.txt | rocq-toplevel-api.tester
  [0] 1 > run 0 "Definition test := nat. XXX"
  Error: while processing the command.
  Trailing text after command: " XXX".
  {}
  [0] 1 > run 42 "Definition test := nat. "
  Error: while processing the command.
  Trailing text after command: " ".
  {}
  [0] 1 > run 0 "Goal 0 = 0."
  {
    "proof_state": {
      "focused_goals": [ "\n============================\n0 = 0" ]
    }
  }
  [0] 2 > run 0 "Proof.   "
  Error: while processing the command.
  Trailing text after command: "   ".
  {}
  [0] 2 > run 0 "Proof."
  {
    "proof_state": {
      "focused_goals": [ "\n============================\n0 = 0" ]
    }
  }
  [0] 3 > run 127 "- reflexivity."
  Error: while processing the command.
  Trailing text after command: " reflexivity.".
  {}
  [0] 3 > run 0 "- "
  Error: while processing the command.
  Trailing text after command: " ".
  {}
  [0] 3 > run 0 " -"
  Error: while processing the command.
  Leading text before command: " ".
  {}
  [0] 3 > run 0 "-"
  {
    "proof_state": {
      "unfocused_goals": [ 0 ],
      "focused_goals": [ "\n============================\n0 = 0" ]
    }
  }
  [0] 4 > run 0 "reflexivity."
  { "proof_state": { "unfocused_goals": [ 0 ] } }
  [0] 5 > run 0 "Qed."
  { "globrefs_diff": { "added_constants": [ "Top.Unnamed_thm" ] } }
  [0] 6 > run 0 "Goal 0 = 0."
  {
    "proof_state": {
      "focused_goals": [ "\n============================\n0 = 0" ]
    }
  }
  [0] 7 > run 0 "Proof."
  {
    "proof_state": {
      "focused_goals": [ "\n============================\n0 = 0" ]
    }
  }
  [0] 8 > run 0 "1:"
  Error: while processing the command.
  Syntax error: [subprf_with_selector] or [ltac_info] or [tactic] expected (in [tactic_command]).
  {
    "error_loc": {
      "fname": [ "ToplevelInput" ],
      "line_nb": 1,
      "bol_pos": 0,
      "line_nb_last": 1,
      "bol_pos_last": 0,
      "bp": 2,
      "ep": 3
    }
  }
  [0] 8 > run 0 "1: reflexivity."
  { "proof_state": {} }
  [0] 9 > run 0 "1:{ "
  Error: while processing the command.
  Trailing text after command: " ".
  {}
  [0] 9 > run 0 "1:{"
  Error: while processing the command.
  [Focus] No such goal (1).
  {
    "error_loc": {
      "fname": [ "ToplevelInput" ],
      "line_nb": 1,
      "bol_pos": 0,
      "line_nb_last": 1,
      "bol_pos_last": 0,
      "bp": 0,
      "ep": 3
    },
    "feedback_messages": [
      {
        "level": "error",
        "loc": {
          "fname": [ "ToplevelInput" ],
          "line_nb": 1,
          "bol_pos": 0,
          "line_nb_last": 1,
          "bol_pos_last": 0,
          "bp": 0,
          "ep": 3
        },
        "text": "[Focus] No such goal (1)."
      }
    ]
  }
  [0] 9 > run 0 "reflexivity."
  Error: while processing the command.
  No such goal.
  {
    "error_loc": {
      "fname": [ "ToplevelInput" ],
      "line_nb": 1,
      "bol_pos": 0,
      "line_nb_last": 1,
      "bol_pos_last": 0,
      "bp": 0,
      "ep": 12
    },
    "feedback_messages": [
      {
        "level": "error",
        "loc": {
          "fname": [ "ToplevelInput" ],
          "line_nb": 1,
          "bol_pos": 0,
          "line_nb_last": 1,
          "bol_pos_last": 0,
          "bp": 0,
          "ep": 12
        },
        "text": "No such goal."
      }
    ]
  }
  [0] 9 > run 246 "} "
  Error: while processing the command.
  Trailing text after command: " ".
  {}
  [0] 9 > run 0 " }"
  Error: while processing the command.
  Leading text before command: " ".
  {}
  [0] 9 > run 0 "}"
  Error: while processing the command.
  The proof is not focused
  {
    "error_loc": {
      "fname": [ "ToplevelInput" ],
      "line_nb": 1,
      "bol_pos": 0,
      "line_nb_last": 1,
      "bol_pos_last": 0,
      "bp": 0,
      "ep": 1
    },
    "feedback_messages": [
      {
        "level": "error",
        "loc": {
          "fname": [ "ToplevelInput" ],
          "line_nb": 1,
          "bol_pos": 0,
          "line_nb_last": 1,
          "bol_pos_last": 0,
          "bp": 0,
          "ep": 1
        },
        "text": "The proof is not focused"
      }
    ]
  }
  [0] 9 > run 0 "Qed."
  { "globrefs_diff": { "added_constants": [ "Top.Unnamed_thm0" ] } }
  [0] 13 > run 0 "  Locate nat."
  Error: while processing the command.
  Leading text before command: "  ".
  {}
  [0] 13 > [EOF]

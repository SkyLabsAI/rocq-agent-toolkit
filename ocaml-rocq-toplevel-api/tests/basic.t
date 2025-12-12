  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ cat > commands.txt <<EOF
  > run 0 "Inductive n := Zero : n | Succ : n -> n."
  > run 0 "Require Import Stdlib.ZArith.BinInt."
  > run 0 "Require Import Stdlib.ZArith.BinIntt"
  > run 0 "Require Import Stdlib.ZArith.BinInk."
  > run 0 "Lemma test : 0 = 0."
  > run 0 "Proof."
  > run 0 "reflexivity."
  > run 0 "Qed."
  > run 37 "About test."
  > back_to 3
  > back_to 8
  > run 37 "About test."
  > EOF

  $ cat commands.txt | rocq-toplevel-api.tester
  [0] 1 > run 0 "Inductive n := Zero : n | Succ : n -> n."
  {
    "globrefs_diff": {
      "added_constants": [
        "Top.n_ind", "Top.n_rec", "Top.n_rect", "Top.n_sind"
      ],
      "added_inductives": [ "Top.n" ]
    },
    "feedback_messages": [
      { "level": "info", "text": "n is defined" },
      { "level": "info", "text": "n_rect is defined" },
      { "level": "info", "text": "n_ind is defined" },
      { "level": "info", "text": "n_rec is defined" },
      { "level": "info", "text": "n_sind is defined" }
    ]
  }
  [0] 2 > run 0 "Require Import Stdlib.ZArith.BinInt."
  {}
  [0] 3 > run 0 "Require Import Stdlib.ZArith.BinIntt"
  Error: while processing the command.
  Syntax error: '.' expected after [gallina_ext] (in [vernac_aux]).
  {
    "error_loc": {
      "fname": [ "ToplevelInput" ],
      "line_nb": 1,
      "bol_pos": 0,
      "line_nb_last": 1,
      "bol_pos_last": 0,
      "bp": 36,
      "ep": 37
    }
  }
  [0] 3 > run 0 "Require Import Stdlib.ZArith.BinInk."
  Error: while processing the command.
  Unable to locate library Stdlib.ZArith.BinInk.
  {
    "error_loc": {
      "fname": [ "ToplevelInput" ],
      "line_nb": 1,
      "bol_pos": 0,
      "line_nb_last": 1,
      "bol_pos_last": 0,
      "bp": 15,
      "ep": 35
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
          "bp": 15,
          "ep": 35
        },
        "text": "Unable to locate library Stdlib.ZArith.BinInk."
      }
    ]
  }
  [0] 3 > run 0 "Lemma test : 0 = 0."
  {
    "proof_state": {
      "focused_goals": [ "\n============================\n0 = 0" ]
    }
  }
  [0] 5 > run 0 "Proof."
  {
    "proof_state": {
      "focused_goals": [ "\n============================\n0 = 0" ]
    }
  }
  [0] 6 > run 0 "reflexivity."
  { "proof_state": {} }
  [0] 7 > run 0 "Qed."
  { "globrefs_diff": { "added_constants": [ "Top.test" ] } }
  [0] 8 > run 37 "About test."
  {
    "feedback_messages": [
      {
        "level": "notice",
        "text": "test : 0 = 0\n\ntest is not universe polymorphic\ntest is opaque\nExpands to: Constant Top.test\nDeclared in toplevel input, characters 6-10"
      }
    ]
  }
  [0] 9 > back_to 3
  [0] 3 > back_to 8
  Error while processing the command.
  Unknown state 8.
  [0] 3 > run 37 "About test."
  {
    "feedback_messages": [
      { "level": "notice", "text": "test not a defined object." }
    ]
  }
  [0] 10 > [EOF]

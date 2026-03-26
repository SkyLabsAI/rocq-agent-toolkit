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
  > run 37 "Fail Qed."
  > run 37 "Time Succeed Timeout 30 About nat."
  > EOF

  $ cat commands.txt | rocq-simple-api.toplevel
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
    ],
    "synterp_ast": { "controls": [], "tag": "Inductive", "pure": true }
  }
  [0] 2 > run 0 "Require Import Stdlib.ZArith.BinInt."
  { "synterp_ast": { "controls": [], "tag": "Require", "pure": false } }
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
    "synterp_ast": { "controls": [], "tag": "StartTheoremProof", "pure": true },
    "proof_state": {
      "focused_goals": [ "\n============================\n0 = 0" ]
    }
  }
  [0] 5 > run 0 "Proof."
  {
    "synterp_ast": { "controls": [], "tag": "Proof", "pure": true },
    "proof_state": {
      "focused_goals": [ "\n============================\n0 = 0" ]
    }
  }
  [0] 6 > run 0 "reflexivity."
  {
    "synterp_ast": { "controls": [], "tag": "Extend", "pure": false },
    "proof_state": {}
  }
  [0] 7 > run 0 "Qed."
  {
    "globrefs_diff": { "added_constants": [ "Top.test" ] },
    "synterp_ast": { "controls": [], "tag": "EndProof", "pure": true }
  }
  [0] 8 > run 37 "About test."
  {
    "feedback_messages": [
      {
        "level": "notice",
        "text": "test : 0 = 0\n\ntest is not universe polymorphic\ntest is opaque\nExpands to: Constant Top.test\nDeclared in toplevel input, characters 6-10"
      }
    ],
    "synterp_ast": { "controls": [], "tag": "Print", "pure": true }
  }
  [0] 9 > back_to 3
  [0] 3 > back_to 8
  Error while processing the command.
  Unknown state 8.
  [0] 3 > run 37 "About test."
  {
    "feedback_messages": [
      { "level": "notice", "text": "test not a defined object." }
    ],
    "synterp_ast": { "controls": [], "tag": "Print", "pure": true }
  }
  [0] 10 > run 37 "Fail Qed."
  {
    "feedback_messages": [
      {
        "level": "notice",
        "text": "The command has indeed failed with message:\nCommand not supported (No proof-editing in progress)."
      }
    ],
    "synterp_ast": { "controls": [ "Fail" ], "tag": "EndProof", "pure": true }
  }
  [0] 11 > run 37 "Time Succeed Timeout 30 About nat."
  {
    "feedback_messages": [
      {
        "level": "notice",
        "text": "nat : Set\n\nnat is not universe polymorphic\nExpands to: Inductive Corelib.Init.Datatypes.nat\nDeclared in library Corelib.Init.Datatypes, line 178, characters 10-13"
      },
      {
        "level": "notice",
        "text": "Finished transaction in 0. secs (0.u,0.s) (successful)"
      }
    ],
    "synterp_ast": {
      "controls": [ "Time", "Succeed", "Timeout" ],
      "tag": "Print",
      "pure": true
    }
  }
  [0] 12 > [EOF]

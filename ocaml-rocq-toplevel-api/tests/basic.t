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
  > run 37 "About test."
  > EOF

  $ cat commands.txt | rocq-toplevel-api.tester
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
  OK
  {}
  OK
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
  Error: Syntax error: '.' expected after [gallina_ext] (in [vernac_aux]).
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
  Error: Unable to locate library Stdlib.ZArith.BinInk.
  {
    "proof_state": {
      "open_subgoals": "1 goal\n  \n  ============================\n  0 = 0"
    }
  }
  OK
  {
    "proof_state": {
      "open_subgoals": "1 goal\n  \n  ============================\n  0 = 0"
    }
  }
  OK
  { "proof_state": { "open_subgoals": "No more goals." } }
  OK
  { "globrefs_diff": { "added_constants": [ "Top.test" ] } }
  OK
  {
    "feedback_messages": [
      {
        "level": "notice",
        "text": "test : 0 = 0\n\ntest is not universe polymorphic\ntest is opaque\nExpands to: Constant Top.test\nDeclared in toplevel input, characters 6-10"
      }
    ]
  }
  OK
  OK
  {
    "feedback_messages": [
      { "level": "notice", "text": "test not a defined object." }
    ]
  }
  OK

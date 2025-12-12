  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ cat > commands.txt <<EOF
  > run 0 "Inductive n := Zero : n | Succ : n -> n."
  > stop 0
  > switch 1
  > stop 1
  > fork 0
  > switch 1
  > run 0 "About n."
  > fork 1
  > stop 0
  > switch 2
  > stop 1
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
  [0] 2 > stop 0
  Error: cannot stop the current toplevel.
  [0] 2 > switch 1
  Error: no toplevel 1.
  [0] 2 > stop 1
  Error: no toplevel 1.
  [0] 2 > fork 0
  New toplevel forked with identifier 1.
  [0] 2 > switch 1
  [1] 2 > run 0 "About n."
  {
    "feedback_messages": [
      {
        "level": "notice",
        "text": "n : Set\n\nn is not universe polymorphic\nExpands to: Inductive Top.n\nDeclared in toplevel input, characters 10-11"
      }
    ]
  }
  [1] 3 > fork 1
  New toplevel forked with identifier 2.
  [1] 3 > stop 0
  [1] 3 > switch 2
  [2] 3 > stop 1
  [2] 3 > [EOF]

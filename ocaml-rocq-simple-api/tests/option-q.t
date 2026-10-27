  $ cat > commands.txt <<EOF
  > run 0 "Locate nat."
  > back_to 1
  > run 0 "Definition test := nat."
  > EOF

  $ cat commands.txt | rocq-simple-api.toplevel -q
  [0] 1 > run 0 "Locate nat."
  {
    "feedback_messages": [
      { "level": "notice", "text": "Inductive Corelib.Init.Datatypes.nat" }
    ],
    "synterp_ast": { "controls": [], "tag": "Locate", "pure": true },
    "loc": {
      "fname": [ "ToplevelInput" ],
      "line_nb": 1,
      "bol_pos": 0,
      "line_nb_last": 1,
      "bol_pos_last": 0,
      "bp": 0,
      "ep": 11
    }
  }
  [0] 2 > back_to 1
  [0] 1 > run 0 "Definition test := nat."
  {
    "globrefs_diff": { "added_constants": [ "Top.test" ] },
    "feedback_messages": [ { "level": "info", "text": "test is defined" } ],
    "synterp_ast": { "controls": [], "tag": "Definition", "pure": true },
    "loc": {
      "fname": [ "ToplevelInput" ],
      "line_nb": 1,
      "bol_pos": 0,
      "line_nb_last": 1,
      "bol_pos_last": 0,
      "bp": 0,
      "ep": 23
    }
  }
  [0] 3 > [EOF]

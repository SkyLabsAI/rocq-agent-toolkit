Sentence splitting uses the current parser state, advances that state between
sentences, and does not change the live toplevel state.  In particular, the
notation introduced only in the split request must not be available to the
following [run].  The prompts also show that [split] leaves the state ID at 2.

  $ cat > commands.txt <<'EOF'
  > run 0 "Notation \"x '+++' y\" := (x + y) (at level 50, left associativity)."
  > split 100 " Check 1 +++ 2. Notation \"x '***' y\" := (x * y) (at level 40, left associativity). Check 2 *** 3."
  > run 0 "Check 2 *** 3."
  > split 10 "  About nat.\n Definition x := "
  > EOF

  $ rocq-simple-api.toplevel < commands.txt
  [0] 1 > run 0 "Notation \"x '+++' y\" := (x + y) (at level 50, left associativity)."
  {
    "synterp_ast": { "controls": [], "tag": "Notation", "pure": false },
    "loc": {
      "fname": [ "ToplevelInput" ],
      "line_nb": 1,
      "bol_pos": 0,
      "line_nb_last": 1,
      "bol_pos_last": 0,
      "bp": 0,
      "ep": 66
    }
  }
  [0] 2 > split 100 " Check 1 +++ 2. Notation \"x '***' y\" := (x * y) (at level 40, left associativity). Check 2 *** 3."
  {
    "items": [
      { "kind": "blanks", "text": " ", "bp": 100, "ep": 101 },
      {
        "kind": { "controls": [], "tag": "CheckMayEval", "pure": true },
        "text": "Check 1 +++ 2.",
        "bp": 101,
        "ep": 115
      },
      { "kind": "blanks", "text": " ", "bp": 115, "ep": 116 },
      {
        "kind": { "controls": [], "tag": "Notation", "pure": false },
        "text": "Notation \"x '***' y\" := (x * y) (at level 40, left associativity).",
        "bp": 116,
        "ep": 182
      },
      { "kind": "blanks", "text": " ", "bp": 182, "ep": 183 },
      {
        "kind": { "controls": [], "tag": "CheckMayEval", "pure": true },
        "text": "Check 2 *** 3.",
        "bp": 183,
        "ep": 197
      }
    ]
  }
  [0] 2 > run 0 "Check 2 *** 3."
  Error: while processing the command.
  Syntax error: '.' expected after [lconstr] (in [query_command]).
  {
    "error_loc": {
      "fname": [ "ToplevelInput" ],
      "line_nb": 1,
      "bol_pos": 0,
      "line_nb_last": 1,
      "bol_pos_last": 0,
      "bp": 8,
      "ep": 10
    }
  }
  [0] 2 > split 10 "  About nat.\n Definition x := "
  Error: while splitting the text.
  {
    "items": [
      { "kind": "blanks", "text": "  ", "bp": 10, "ep": 12 },
      {
        "kind": { "controls": [], "tag": "Print", "pure": true },
        "text": "About nat.",
        "bp": 12,
        "ep": 22
      },
      { "kind": "blanks", "text": "\n ", "bp": 22, "ep": 24 }
    ],
    "leftover": "Definition x := ",
    "error": "Syntax error: [reduce] expected after ':=' (in [def_body]).",
    "loc": {
      "fname": [ "ToplevelInput" ],
      "line_nb": 2,
      "bol_pos": 23,
      "line_nb_last": 2,
      "bol_pos_last": 23,
      "bp": 40,
      "ep": 41
    }
  }
  [0] 2 > [EOF]

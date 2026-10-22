Location advancement accepts only blank characters and comments. It reports the
location after those characters without changing the toplevel state, rejects an
actual token, and returns errors for invalid lexer input without stopping the
toplevel.

  $ cat > commands.txt <<'EOF'
  > loc_after_blanks 0 " \n(* comment *)\n  "
  > loc_after_blanks 0 " \n(* comment *) Check."
  > loc_after_blanks 0 "$"
  > loc_after_blanks 0 "\255"
  > loc_after_blanks 0 "(* unterminated"
  > loc_after_blanks 0 "  "
  > EOF

  $ rocq-simple-api.toplevel < commands.txt
  [0] 1 > loc_after_blanks 0 " \n(* comment *)\n  "
  {
    "fname": [ "ToplevelInput" ],
    "line_nb": 3,
    "bol_pos": 16,
    "line_nb_last": 3,
    "bol_pos_last": 16,
    "bp": 18,
    "ep": 18
  }
  [0] 1 > loc_after_blanks 0 " \n(* comment *) Check."
  Error: while advancing the location.
  Expected only blank characters and comments, but found token "Check".
  [0] 1 > loc_after_blanks 0 "$"
  Error: while advancing the location.
  Syntax Error: Lexer: Undefined token
  [0] 1 > loc_after_blanks 0 "\255"
  Error: while advancing the location.
  Syntax Error: Lexer: Illegal character
  [0] 1 > loc_after_blanks 0 "(* unterminated"
  Error: while advancing the location.
  Syntax Error: Lexer: Unterminated comment
  [0] 1 > loc_after_blanks 0 "  "
  {
    "fname": [ "ToplevelInput" ],
    "line_nb": 1,
    "bol_pos": 0,
    "line_nb_last": 1,
    "bol_pos_last": 0,
    "bp": 2,
    "ep": 2
  }
  [0] 1 > [EOF]

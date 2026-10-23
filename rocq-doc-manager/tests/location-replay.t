This test exercises location-aware replay across diverging clones.  The shared
prefix includes multiline text, UTF-8 in blanks, and a ghost command.  Cursor 1
is materialized while out of sync, so its fork must roll back the other branch
and replay its own blanks before accepting more commands.

  $ : > test.v
  $ cat > calls.txt <<'EOF'
  > insert_command [0,"Definition base :=\n  nat.",false]
  > insert_blanks [0,"\n(* λ shared *)\n"]
  > insert_command [0,"Definition hidden_shared := base.",true]
  > insert_command [0,"Definition shared := base.",false]
  > insert_blanks [0,"\n"]
  > clone [0]
  > insert_command [0,"Definition left :=\n  shared.",false]
  > insert_blanks [0,"\n\n"]
  > insert_blanks [1,"(* branch one *)\n\n"]
  > materialize [1]
  > insert_command [1,"Definition hidden_right := shared.",true]
  > insert_command [1,"Definition right := shared.",false]
  > insert_blanks [1,"\n"]
  > clone [0]
  > insert_command [0,"Definition left2 := left.",false]
  > insert_blanks [0,"\n"]
  > insert_blanks [2,"(* branch two *)\n"]
  > insert_command [2,"Definition hidden_alt := left.",true]
  > insert_command [2,"Definition alt := left.",false]
  > insert_blanks [2,"\n"]
  > query_text [0,"Check left2.",0]
  > query_text [2,"Check alt.",0]
  > copy_contents [1,2]
  > query_text [2,"Check hidden_right.",0]
  > query_text [2,"Check right.",0]
  > insert_command [2,"Check right.",false]
  > query_text [0,"Check left2.",0]
  > query_text [1,"Check hidden_right.",0]
  > EOF

Copying the materialized branch back onto cursor 2 forces a second backend to
roll back a divergent prefix and replay blanks, ordinary commands, and the
stored ghost command.  The final queries repeatedly switch the shared backend
between divergent branches.  Besides checking that every replay completes, we
retain command locations to verify that replay preserves line and byte data.
Ghost commands intentionally execute at the initial source location and do not
advance the document cursor.

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap > commands.txt
  $ cat commands.txt | rocq-doc-manager test.v -- -Q . test.dir | jsonrpc-tp.tp_unwrap | grep -E '^  "id":|^      "(line_nb|bol_pos|line_nb_last|bol_pos_last|bp|ep)":|^\{ "id":'
    "id": 1,
        "line_nb": 1,
        "bol_pos": 0,
        "line_nb_last": 2,
        "bol_pos_last": 19,
        "bp": 0,
        "ep": 25
  { "id": 2, "jsonrpc": "2.0", "result": null }
    "id": 3,
        "line_nb": 1,
        "bol_pos": 0,
        "line_nb_last": 1,
        "bol_pos_last": 0,
        "bp": 0,
        "ep": 33
    "id": 4,
        "line_nb": 4,
        "bol_pos": 42,
        "line_nb_last": 4,
        "bol_pos_last": 42,
        "bp": 42,
        "ep": 68
  { "id": 5, "jsonrpc": "2.0", "result": null }
  { "id": 6, "jsonrpc": "2.0", "result": 1 }
    "id": 7,
        "line_nb": 5,
        "bol_pos": 69,
        "line_nb_last": 6,
        "bol_pos_last": 88,
        "bp": 69,
        "ep": 97
  { "id": 8, "jsonrpc": "2.0", "result": null }
  { "id": 9, "jsonrpc": "2.0", "result": null }
  { "id": 10, "jsonrpc": "2.0", "result": null }
    "id": 11,
        "line_nb": 1,
        "bol_pos": 0,
        "line_nb_last": 1,
        "bol_pos_last": 0,
        "bp": 0,
        "ep": 34
    "id": 12,
        "line_nb": 7,
        "bol_pos": 87,
        "line_nb_last": 7,
        "bol_pos_last": 87,
        "bp": 87,
        "ep": 114
  { "id": 13, "jsonrpc": "2.0", "result": null }
  { "id": 14, "jsonrpc": "2.0", "result": 2 }
    "id": 15,
        "line_nb": 8,
        "bol_pos": 99,
        "line_nb_last": 8,
        "bol_pos_last": 99,
        "bp": 99,
        "ep": 124
  { "id": 16, "jsonrpc": "2.0", "result": null }
  { "id": 17, "jsonrpc": "2.0", "result": null }
    "id": 18,
        "line_nb": 1,
        "bol_pos": 0,
        "line_nb_last": 1,
        "bol_pos_last": 0,
        "bp": 0,
        "ep": 30
    "id": 19,
        "line_nb": 9,
        "bol_pos": 116,
        "line_nb_last": 9,
        "bol_pos_last": 116,
        "bp": 116,
        "ep": 139
  { "id": 20, "jsonrpc": "2.0", "result": null }
  { "id": 21, "jsonrpc": "2.0", "result": "left2\n     : Set" }
  { "id": 22, "jsonrpc": "2.0", "result": "alt\n     : Set" }
  { "id": 23, "jsonrpc": "2.0", "result": null }
  { "id": 24, "jsonrpc": "2.0", "result": "hidden_right\n     : Set" }
  { "id": 25, "jsonrpc": "2.0", "result": "right\n     : Set" }
    "id": 26,
        "line_nb": 8,
        "bol_pos": 115,
        "line_nb_last": 8,
        "bol_pos_last": 115,
        "bp": 115,
        "ep": 127
  { "id": 27, "jsonrpc": "2.0", "result": "left2\n     : Set" }
  { "id": 28, "jsonrpc": "2.0", "result": "hidden_right\n     : Set" }

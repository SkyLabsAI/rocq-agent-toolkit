  $ cat > test.v <<EOF
  > (* This is an ill-formed file. *)
  > About nat.
  > 
  > (* Ill-formed command. *)
  > Definition incomplete :=
  > EOF

  $ rocq-split test.v -- -Q . test.dir
  {
    "error": "Syntax error: [reduce] expected after ':=' (in [def_body]).",
    "loc": {
      "fname": [ "InFile", { "dirpath": null, "file": "test.v" } ],
      "line_nb": 6,
      "bol_pos": 97,
      "line_nb_last": 6,
      "bol_pos_last": 97,
      "bp": 97,
      "ep": 98
    },
    "Items": [
      {
        "kind": "blanks",
        "text": "(* This is an ill-formed file. *)\n",
        "bp": 0,
        "ep": 34
      },
      {
        "kind": { "tag": "Print", "pure": true },
        "text": "About nat.",
        "bp": 34,
        "ep": 44
      },
      {
        "kind": "blanks",
        "text": "\n\n(* Ill-formed command. *)\n",
        "bp": 44,
        "ep": 72
      }
    ]
  }
  [1]

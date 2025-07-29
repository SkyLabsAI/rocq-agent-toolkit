  $ cat > test.v <<EOF
  > (* This is an ill-formed file. *)
  > Definition incomplete :=
  > EOF

  $ rocq_split -Q . test.dir test.v
  {
    "error": "Syntax error: [reduce] expected after ':=' (in [def_body]).",
    "loc": {
      "fname": [ "InFile", { "dirpath": null, "file": "test.v" } ],
      "line_nb": 3,
      "bol_pos": 59,
      "line_nb_last": 3,
      "bol_pos_last": 59,
      "bp": 59,
      "ep": 60
    }
  }
  [1]

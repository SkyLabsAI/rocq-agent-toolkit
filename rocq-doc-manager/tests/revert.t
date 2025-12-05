  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v <<EOF
  > Definition test := nat.
  > About nat.
  > Check test.
  > EOF

  $ cat > calls.txt <<EOF
  > load_file
  > doc_suffix
  > run_step
  > run_step
  > run_step
  > revert_before {erase:false,index:2}
  > revert_before {erase:false,index:2}
  > revert_before {erase:true,index:0}
  > doc_prefix
  > doc_suffix
  > run_step
  > run_step
  > run_step
  > revert_before {erase:false,index:0}
  > revert_before {erase:false,index:0}
  > EOF

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap > commands.txt

  $ cat commands.txt | rocq-doc-manager test.v -- -Q . test.dir | jsonrpc-tp.tp_unwrap
  { "id": 1, "jsonrpc": "2.0", "result": null }
  {
    "id": 2,
    "jsonrpc": "2.0",
    "result": [
      { "kind": "command", "text": "Definition test := nat." },
      { "kind": "blanks", "text": "\n" },
      { "kind": "command", "text": "About nat." },
      { "kind": "blanks", "text": "\n" },
      { "kind": "command", "text": "Check test." }
    ]
  }
  {
    "id": 3,
    "jsonrpc": "2.0",
    "result": {
      "globrefs_diff": { "added_constants": [ "test.dir.test.test" ] },
      "feedback_messages": [ { "level": "info", "text": "test is defined" } ]
    }
  }
  { "id": 4, "jsonrpc": "2.0", "result": null }
  {
    "id": 5,
    "jsonrpc": "2.0",
    "result": {
      "feedback_messages": [
        {
          "level": "notice",
          "text": "nat : Set\n\nnat is not universe polymorphic\nExpands to: Inductive Corelib.Init.Datatypes.nat\nDeclared in library Corelib.Init.Datatypes, line 178, characters 10-13"
        }
      ]
    }
  }
  { "id": 6, "jsonrpc": "2.0", "result": null }
  { "id": 7, "jsonrpc": "2.0", "result": null }
  { "id": 8, "jsonrpc": "2.0", "result": null }
  { "id": 9, "jsonrpc": "2.0", "result": [] }
  {
    "id": 10,
    "jsonrpc": "2.0",
    "result": [
      { "kind": "command", "text": "About nat." },
      { "kind": "blanks", "text": "\n" },
      { "kind": "command", "text": "Check test." }
    ]
  }
  {
    "id": 11,
    "jsonrpc": "2.0",
    "result": {
      "feedback_messages": [
        {
          "level": "notice",
          "text": "nat : Set\n\nnat is not universe polymorphic\nExpands to: Inductive Corelib.Init.Datatypes.nat\nDeclared in library Corelib.Init.Datatypes, line 178, characters 10-13"
        }
      ]
    }
  }
  { "id": 12, "jsonrpc": "2.0", "result": null }
  {
    "id": 13,
    "jsonrpc": "2.0",
    "error": {
      "data": {
        "error_loc": {
          "line_nb": 1,
          "bol_pos": 0,
          "line_nb_last": 1,
          "bol_pos_last": 0,
          "bp": 51,
          "ep": 55
        },
        "feedback_messages": [
          {
            "level": "error",
            "loc": {
              "line_nb": 1,
              "bol_pos": 0,
              "line_nb_last": 1,
              "bol_pos_last": 0,
              "bp": 51,
              "ep": 55
            },
            "text": "The reference test was not found in the current environment."
          }
        ]
      },
      "code": -32803,
      "message": "The reference test was not found in the current environment."
    }
  }
  { "id": 14, "jsonrpc": "2.0", "result": null }
  { "id": 15, "jsonrpc": "2.0", "result": null }

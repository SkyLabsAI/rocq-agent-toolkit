  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v <<EOF
  > (** comment x1 *)
  > Definition x1 := nat.
  > (** comment x2 *)
  > Definition x2 := nat.
  > EOF

  $ cat > calls.txt <<EOF
  > load_file [0]
  > clone [0]
  > run_step [0]
  > run_step [0]
  > query_text [0,"Check x1.",0]
  > query_text [1,"Check x1.",0]
  > insert_blanks [0,"\n(* inserted comment *)\n"]
  > query_text [0,"Check x1.",0]
  > query_text [1,"Check x1.",0]
  > insert_command [0,"Definition inserted := nat.",false]
  > query_text [0,"Check x1.",0]
  > query_text [1,"Check x1.",0]
  > insert_blanks [0,"\n"]
  > query_text [0,"Check x1.",0]
  > query_text [1,"Check x1.",0]
  > EOF

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap > commands.txt

  $ cat commands.txt | rocq-doc-manager test.v -- -Q . test.dir | jsonrpc-tp.tp_unwrap
  { "method": "ready_seq", "jsonrpc": "2.0" }
  { "id": 1, "jsonrpc": "2.0", "result": null }
  { "id": 2, "jsonrpc": "2.0", "result": 1 }
  { "id": 3, "jsonrpc": "2.0", "result": null }
  {
    "id": 4,
    "jsonrpc": "2.0",
    "result": {
      "globrefs_diff": { "added_constants": [ "test.dir.test.x1" ] },
      "feedback_messages": [ { "level": "info", "text": "x1 is defined" } ]
    }
  }
  { "id": 5, "jsonrpc": "2.0", "result": "x1\n     : Set" }
  {
    "id": 6,
    "jsonrpc": "2.0",
    "error": {
      "code": -32803,
      "message": "The reference x1 was not found in the current environment."
    }
  }
  { "id": 7, "jsonrpc": "2.0", "result": null }
  { "id": 8, "jsonrpc": "2.0", "result": "x1\n     : Set" }
  {
    "id": 9,
    "jsonrpc": "2.0",
    "error": {
      "code": -32803,
      "message": "The reference x1 was not found in the current environment."
    }
  }
  {
    "id": 10,
    "jsonrpc": "2.0",
    "result": {
      "globrefs_diff": { "added_constants": [ "test.dir.test.inserted" ] },
      "feedback_messages": [
        { "level": "info", "text": "inserted is defined" }
      ]
    }
  }
  { "id": 11, "jsonrpc": "2.0", "result": "x1\n     : Set" }
  {
    "id": 12,
    "jsonrpc": "2.0",
    "error": {
      "code": -32803,
      "message": "The reference x1 was not found in the current environment."
    }
  }
  { "id": 13, "jsonrpc": "2.0", "result": null }
  { "id": 14, "jsonrpc": "2.0", "result": "x1\n     : Set" }
  {
    "id": 15,
    "jsonrpc": "2.0",
    "error": {
      "code": -32803,
      "message": "The reference x1 was not found in the current environment."
    }
  }

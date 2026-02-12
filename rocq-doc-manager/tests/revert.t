  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v <<EOF
  > Definition test := nat.
  > About nat.
  > Check test.
  > EOF

  $ cat > calls.txt <<EOF
  > load_file [0]
  > doc_suffix [0]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > revert_before [0,{erase:false,index:2}]
  > revert_before [0,{erase:false,index:2}]
  > revert_before [0,{erase:true,index:0}]
  > doc_prefix [0]
  > doc_suffix [0]
  > run_step [0]
  > run_step [0]
  > run_step [0]
  > revert_before [0,{erase:false,index:0}]
  > revert_before [0,{erase:false,index:0}]
  > EOF

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap > commands.txt

  $ cat commands.txt | rocq-doc-manager test.v -- -Q . test.dir | jsonrpc-tp.tp_unwrap
  { "method": "ready_seq", "jsonrpc": "2.0" }
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
  {
    "id": 6,
    "jsonrpc": "2.0",
    "error": {
      "code": -32602,
      "message": "Invalid parameters for method revert_before: Ill-typed argument 'erase': expected boolean value."
    }
  }
  {
    "id": 7,
    "jsonrpc": "2.0",
    "error": {
      "code": -32602,
      "message": "Invalid parameters for method revert_before: Ill-typed argument 'erase': expected boolean value."
    }
  }
  {
    "id": 8,
    "jsonrpc": "2.0",
    "error": {
      "code": -32602,
      "message": "Invalid parameters for method revert_before: Ill-typed argument 'erase': expected boolean value."
    }
  }
  {
    "id": 9,
    "jsonrpc": "2.0",
    "result": [
      { "kind": "command", "offset": 0, "text": "Definition test := nat." },
      { "kind": "blanks", "offset": 23, "text": "\n" },
      { "kind": "command", "offset": 24, "text": "About nat." }
    ]
  }
  {
    "id": 10,
    "jsonrpc": "2.0",
    "result": [
      { "kind": "blanks", "text": "\n" },
      { "kind": "command", "text": "Check test." }
    ]
  }
  { "id": 11, "jsonrpc": "2.0", "result": null }
  {
    "id": 12,
    "jsonrpc": "2.0",
    "result": {
      "feedback_messages": [
        { "level": "notice", "text": "test\n     : Set" }
      ]
    }
  }
  {
    "id": 13,
    "jsonrpc": "2.0",
    "error": {
      "code": -32602,
      "message": "Invalid parameters for method run_step: no step left to run."
    }
  }
  {
    "id": 14,
    "jsonrpc": "2.0",
    "error": {
      "code": -32602,
      "message": "Invalid parameters for method revert_before: Ill-typed argument 'erase': expected boolean value."
    }
  }
  {
    "id": 15,
    "jsonrpc": "2.0",
    "error": {
      "code": -32602,
      "message": "Invalid parameters for method revert_before: Ill-typed argument 'erase': expected boolean value."
    }
  }

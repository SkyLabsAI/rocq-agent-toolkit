  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v <<EOF
  > Definition test1 := nat.
  > Definition test2 := nat.
  > Definition test3 := nat.
  > EOF

  $ cat > calls.txt <<EOF
  > cursor_index [0]
  > replace_suffix [0,"Definition test4 := 0.",null]
  > cursor_index [0]
  > doc_suffix [0]
  > run_step [0]
  > replace_suffix [0,"\nDefinition my_test := test4 + 1.\n",null]
  > doc_suffix [0]
  > cursor_index [0]
  > run_step [0]
  > run_step [0]
  > go_to [0,0]
  > doc_suffix [0]
  > replace_suffix [0,"Definition foo := 0.",null]
  > run_step [0]
  > replace_suffix [0,"Definition baz := 0.",null]
  > doc_suffix [0]
  > EOF

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap > commands.txt

  $ cat commands.txt | rocq-doc-manager test.v -- -Q . test.dir | jsonrpc-tp.tp_unwrap
  { "method": "ready_seq", "jsonrpc": "2.0" }
  { "id": 1, "jsonrpc": "2.0", "result": 0 }
  {
    "id": 2,
    "jsonrpc": "2.0",
    "result": [
      {
        "kind": "command",
        "text": "Definition test4 := 0.",
        "data": {
          "kind": "Definition",
          "pure": true,
          "attrs": { "id": "test4", "kind": "Definition", "proof": false }
        }
      }
    ]
  }
  { "id": 3, "jsonrpc": "2.0", "result": 0 }
  {
    "id": 4,
    "jsonrpc": "2.0",
    "result": [
      {
        "kind": "command",
        "text": "Definition test4 := 0.",
        "data": {
          "kind": "Definition",
          "pure": true,
          "attrs": { "id": "test4", "kind": "Definition", "proof": false }
        }
      }
    ]
  }
  {
    "id": 5,
    "jsonrpc": "2.0",
    "result": {
      "globrefs_diff": { "added_constants": [ "test.dir.test.test4" ] },
      "feedback_messages": [ { "level": "info", "text": "test4 is defined" } ],
      "synterp_ast": {
        "kind": "Definition",
        "pure": true,
        "attrs": { "id": "test4", "kind": "Definition", "proof": false }
      }
    }
  }
  {
    "id": 6,
    "jsonrpc": "2.0",
    "result": [
      { "kind": "blanks", "text": "\n" },
      {
        "kind": "command",
        "text": "Definition my_test := test4 + 1.",
        "data": {
          "kind": "Definition",
          "pure": true,
          "attrs": { "id": "my_test", "kind": "Definition", "proof": false }
        }
      },
      { "kind": "blanks", "text": "\n" }
    ]
  }
  {
    "id": 7,
    "jsonrpc": "2.0",
    "result": [
      { "kind": "blanks", "text": "\n" },
      {
        "kind": "command",
        "text": "Definition my_test := test4 + 1.",
        "data": {
          "kind": "Definition",
          "pure": true,
          "attrs": { "id": "my_test", "kind": "Definition", "proof": false }
        }
      },
      { "kind": "blanks", "text": "\n" }
    ]
  }
  { "id": 8, "jsonrpc": "2.0", "result": 1 }
  { "id": 9, "jsonrpc": "2.0", "result": null }
  {
    "id": 10,
    "jsonrpc": "2.0",
    "result": {
      "globrefs_diff": { "added_constants": [ "test.dir.test.my_test" ] },
      "feedback_messages": [
        { "level": "info", "text": "my_test is defined" }
      ],
      "synterp_ast": {
        "kind": "Definition",
        "pure": true,
        "attrs": { "id": "my_test", "kind": "Definition", "proof": false }
      }
    }
  }
  { "id": 11, "jsonrpc": "2.0", "result": null }
  {
    "id": 12,
    "jsonrpc": "2.0",
    "result": [
      {
        "kind": "command",
        "text": "Definition test4 := 0.",
        "data": {
          "kind": "Definition",
          "pure": true,
          "attrs": { "id": "test4", "kind": "Definition", "proof": false }
        }
      },
      { "kind": "blanks", "text": "\n" },
      {
        "kind": "command",
        "text": "Definition my_test := test4 + 1.",
        "data": {
          "kind": "Definition",
          "pure": true,
          "attrs": { "id": "my_test", "kind": "Definition", "proof": false }
        }
      },
      { "kind": "blanks", "text": "\n" }
    ]
  }
  {
    "id": 13,
    "jsonrpc": "2.0",
    "result": [
      {
        "kind": "command",
        "text": "Definition foo := 0.",
        "data": {
          "kind": "Definition",
          "pure": true,
          "attrs": { "id": "foo", "kind": "Definition", "proof": false }
        }
      }
    ]
  }
  {
    "id": 14,
    "jsonrpc": "2.0",
    "result": {
      "globrefs_diff": { "added_constants": [ "test.dir.test.foo" ] },
      "feedback_messages": [ { "level": "info", "text": "foo is defined" } ],
      "synterp_ast": {
        "kind": "Definition",
        "pure": true,
        "attrs": { "id": "foo", "kind": "Definition", "proof": false }
      }
    }
  }
  {
    "id": 15,
    "jsonrpc": "2.0",
    "error": {
      "code": -32602,
      "message": "Invalid parameters for method replace_suffix: leading blanks required at this point in the document."
    }
  }
  { "id": 16, "jsonrpc": "2.0", "result": [] }

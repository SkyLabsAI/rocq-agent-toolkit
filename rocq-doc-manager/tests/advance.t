  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v <<EOF
  > Definition n0 : nat := 0.
  > Definition n2 : nat := 2.
  > Definition n4 : nat := 4.
  > Definition n6 : nat := 6.
  > Definition n8 : nat := 8.
  > EOF

  $ cat > calls.txt <<EOF
  > load_file
  > advance_to [4]
  > advance_to [4]
  > doc_suffix
  > advance_to [9]
  > doc_suffix
  > advance_to [10]
  > EOF

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap > commands.txt

  $ cat commands.txt | rocq-doc-manager test.v -- -Q . test.dir | jsonrpc-tp.tp_unwrap
  { "id": 1, "jsonrpc": "2.0", "result": null }
  { "id": 2, "jsonrpc": "2.0", "result": null }
  { "id": 3, "jsonrpc": "2.0", "result": null }
  {
    "id": 4,
    "jsonrpc": "2.0",
    "result": [
      { "kind": "command", "text": "Definition n4 : nat := 4." },
      { "kind": "blanks", "text": "\n" },
      { "kind": "command", "text": "Definition n6 : nat := 6." },
      { "kind": "blanks", "text": "\n" },
      { "kind": "command", "text": "Definition n8 : nat := 8." }
    ]
  }
  { "id": 5, "jsonrpc": "2.0", "result": null }
  { "id": 6, "jsonrpc": "2.0", "result": [] }
  {
    "id": 7,
    "jsonrpc": "2.0",
    "error": {
      "code": -32602,
      "message": "Invalid parameters for method advance_to: index out of bounds."
    }
  }

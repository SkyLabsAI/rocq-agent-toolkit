  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v <<EOF
  > Definition test1 := nat.
  > Definition test2 := nat.
  > Definition test3 := nat.
  > EOF

  $ cat > calls.txt <<EOF
  > cursor_index
  > load_file
  > cursor_index
  > run_step
  > cursor_index
  > run_step
  > cursor_index
  > run_step
  > cursor_index
  > run_step
  > cursor_index
  > run_step
  > cursor_index
  > run_step
  > cursor_index
  > EOF

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap > commands.txt

  $ cat commands.txt | rocq-doc-manager test.v -- -Q . test.dir | jsonrpc-tp.tp_unwrap
  { "id": 1, "jsonrpc": "2.0", "result": 0 }
  { "id": 2, "jsonrpc": "2.0", "result": null }
  { "id": 3, "jsonrpc": "2.0", "result": 0 }
  {
    "id": 4,
    "jsonrpc": "2.0",
    "result": {
      "open_subgoals": null,
      "new_constants": [ "test.dir.test.test1" ]
    }
  }
  { "id": 5, "jsonrpc": "2.0", "result": 1 }
  { "id": 6, "jsonrpc": "2.0", "result": null }
  { "id": 7, "jsonrpc": "2.0", "result": 2 }
  {
    "id": 8,
    "jsonrpc": "2.0",
    "result": {
      "open_subgoals": null,
      "new_constants": [ "test.dir.test.test2" ]
    }
  }
  { "id": 9, "jsonrpc": "2.0", "result": 3 }
  { "id": 10, "jsonrpc": "2.0", "result": null }
  { "id": 11, "jsonrpc": "2.0", "result": 4 }
  {
    "id": 12,
    "jsonrpc": "2.0",
    "result": {
      "open_subgoals": null,
      "new_constants": [ "test.dir.test.test3" ]
    }
  }
  { "id": 13, "jsonrpc": "2.0", "result": 5 }
  {
    "id": 14,
    "jsonrpc": "2.0",
    "error": {
      "data": { "loc": null },
      "code": -32803,
      "message": "no step left to run"
    }
  }
  { "id": 15, "jsonrpc": "2.0", "result": 5 }

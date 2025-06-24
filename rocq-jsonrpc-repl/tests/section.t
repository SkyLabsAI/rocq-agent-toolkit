  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ cat > calls.txt <<EOF
  > run [0,"Section test."]
  > run [0,"Context (n : nat)."]
  > run [0,"Definition get := n."]
  > run [0,"End test."]
  > run [0,"Check get."]
  > quit
  > EOF

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap > commands.txt

  $ cat commands.txt | rocq-jsonrpc-repl | jsonrpc-tp.tp_unwrap
  { "id": 1, "jsonrpc": "2.0", "result": { "success": true, "state": 2 } }
  {
    "id": 2,
    "jsonrpc": "2.0",
    "result": {
      "success": true,
      "state": 3,
      "feedback": [ { "kind": "info", "text": "n is declared" } ]
    }
  }
  {
    "id": 3,
    "jsonrpc": "2.0",
    "result": {
      "success": true,
      "state": 4,
      "data": { "new_constants": [ "Top.get" ] },
      "feedback": [ { "kind": "info", "text": "get is defined" } ]
    }
  }
  { "id": 4, "jsonrpc": "2.0", "result": { "success": true, "state": 5 } }
  {
    "id": 5,
    "jsonrpc": "2.0",
    "result": {
      "success": true,
      "state": 6,
      "feedback": [ { "kind": "notice", "text": "get\n     : nat -> nat" } ]
    }
  }
  { "id": 6, "jsonrpc": "2.0", "result": null }

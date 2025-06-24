  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ cat > calls.txt <<EOF
  > run [0,"Module foo."]
  > run [0,"Definition a := nat."]
  > run [0,"Module Type bar."]
  > run [0,"Definition b := nat."]
  > run [0,"End bar."]
  > run [0,"End foo."]
  > quit
  > EOF

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap > commands.txt

  $ cat commands.txt | rocq-jsonrpc-repl | jsonrpc-tp.tp_unwrap
  {
    "id": 1,
    "jsonrpc": "2.0",
    "result": {
      "success": true,
      "state": 2,
      "feedback": [
        { "kind": "info", "text": "Interactive Module foo started" }
      ]
    }
  }
  {
    "id": 2,
    "jsonrpc": "2.0",
    "result": {
      "success": true,
      "state": 3,
      "data": { "new_constants": [ "Top.foo.a" ] },
      "feedback": [ { "kind": "info", "text": "a is defined" } ]
    }
  }
  {
    "id": 3,
    "jsonrpc": "2.0",
    "result": {
      "success": true,
      "state": 4,
      "feedback": [
        { "kind": "info", "text": "Interactive Module Type bar started" }
      ]
    }
  }
  {
    "id": 4,
    "jsonrpc": "2.0",
    "result": {
      "success": true,
      "state": 5,
      "data": { "new_constants": [ "Top.foo.bar.b" ] },
      "feedback": [ { "kind": "info", "text": "b is defined" } ]
    }
  }
  {
    "id": 5,
    "jsonrpc": "2.0",
    "result": {
      "success": true,
      "state": 6,
      "data": { "removed_constants": [ "Top.foo.bar.b" ] },
      "feedback": [ { "kind": "info", "text": "Module Type bar is defined" } ]
    }
  }
  {
    "id": 6,
    "jsonrpc": "2.0",
    "result": {
      "success": true,
      "state": 7,
      "feedback": [ { "kind": "info", "text": "Module foo is defined" } ]
    }
  }
  { "id": 7, "jsonrpc": "2.0", "result": null }

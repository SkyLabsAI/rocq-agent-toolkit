  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v

  $ cat > calls.txt <<EOF
  > query_text [0,{text:"About nil.",index:0}]
  > query_text [0,{text:"About nil.",index:1}]
  > query_json [0,{text:"About nil.",index:0}]
  > query_text_all [0,{text:"Eval lazy in I.",indices:[]}]
  > query_text_all [0,{text:"Eval lazy in I.",indices:[0]}]
  > query_text_all [0,{text:"Eval lazy in I.",indices:[0,0]}]
  > run_command [0,"Goal True."]
  > query_text_all [0,{text:"idtac \"hello,\"; idtac \"world!\".",indices:null}]
  > run_command [0,"Abort."]
  > EOF

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap > commands.txt

  $ cat commands.txt | rocq-doc-manager test.v -- -Q . test.dir | jsonrpc-tp.tp_unwrap
  {
    "id": 1,
    "jsonrpc": "2.0",
    "error": {
      "code": -32602,
      "message": "Invalid parameters for method query_text: Ill-typed argument 'text': expected string value."
    }
  }
  {
    "id": 2,
    "jsonrpc": "2.0",
    "error": {
      "code": -32602,
      "message": "Invalid parameters for method query_text: Ill-typed argument 'text': expected string value."
    }
  }
  {
    "id": 3,
    "jsonrpc": "2.0",
    "error": {
      "code": -32602,
      "message": "Invalid parameters for method query_json: Ill-typed argument 'text': expected string value."
    }
  }
  {
    "id": 4,
    "jsonrpc": "2.0",
    "error": {
      "code": -32602,
      "message": "Invalid parameters for method query_text_all: Ill-typed argument 'text': expected string value."
    }
  }
  {
    "id": 5,
    "jsonrpc": "2.0",
    "error": {
      "code": -32602,
      "message": "Invalid parameters for method query_text_all: Ill-typed argument 'text': expected string value."
    }
  }
  {
    "id": 6,
    "jsonrpc": "2.0",
    "error": {
      "code": -32602,
      "message": "Invalid parameters for method query_text_all: Ill-typed argument 'text': expected string value."
    }
  }
  {
    "id": 7,
    "jsonrpc": "2.0",
    "result": {
      "proof_state": {
        "given_up_goals": 0,
        "shelved_goals": 0,
        "focused_goals": [ "\n============================\nTrue" ]
      }
    }
  }
  {
    "id": 8,
    "jsonrpc": "2.0",
    "error": {
      "code": -32602,
      "message": "Invalid parameters for method query_text_all: Ill-typed argument 'text': expected string value."
    }
  }
  { "id": 9, "jsonrpc": "2.0", "result": {} }

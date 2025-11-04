  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v

  $ cat > calls.txt <<EOF
  > text_query {text:"About nil.",index:0}
  > text_query {text:"About nil.",index:1}
  > json_query {text:"About nil.",index:0}
  > text_query_all {text:"Eval lazy in I.",indices:[]}
  > text_query_all {text:"Eval lazy in I.",indices:[0]}
  > text_query_all {text:"Eval lazy in I.",indices:[0,0]}
  > run_command ["Goal True."]
  > text_query_all {text:"idtac \"hello,\"; idtac \"world!\".",indices:null}
  > run_command ["Abort."]
  > EOF

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap > commands.txt

  $ cat commands.txt | rocq-doc-manager test.v -- -Q . test.dir | jsonrpc-tp.tp_unwrap
  {
    "id": 1,
    "jsonrpc": "2.0",
    "result": "nil : forall {A : Type}, list A\n\nnil is template universe polymorphic\nArguments nil {A}%_type_scope\nExpands to: Constructor Corelib.Init.Datatypes.nil\nDeclared in library Corelib.Init.Datatypes, line 319, characters 3-6"
  }
  {
    "id": 2,
    "jsonrpc": "2.0",
    "error": {
      "code": -32803,
      "message": "no \"info\" / \"notice\" feedback at the given index"
    }
  }
  {
    "id": 3,
    "jsonrpc": "2.0",
    "error": {
      "code": -32803,
      "message": "the query result does not contain valid JSON"
    }
  }
  { "id": 4, "jsonrpc": "2.0", "result": [] }
  { "id": 5, "jsonrpc": "2.0", "result": [ "     = I\n     : True" ] }
  {
    "id": 6,
    "jsonrpc": "2.0",
    "result": [ "     = I\n     : True", "     = I\n     : True" ]
  }
  {
    "id": 7,
    "jsonrpc": "2.0",
    "result": {
      "open_subgoals": "1 goal\n  \n  ============================\n  True"
    }
  }
  { "id": 8, "jsonrpc": "2.0", "result": [ "hello,", "world!" ] }
  { "id": 9, "jsonrpc": "2.0", "result": {} }

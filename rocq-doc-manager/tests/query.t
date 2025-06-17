  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v

  $ cat > calls.txt <<EOF
  > text_query ["About nil.",0]
  > text_query ["About nil.",1]
  > json_query ["About nil.",0]
  > EOF

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap > commands.txt

  $ cat commands.txt | rocq-doc-manager -Q . test.dir test.v | jsonrpc-tp.tp_unwrap
  {"id":1,"jsonrpc":"2.0","result":"nil : forall {A : Type}, list A\n\nnil is template universe polymorphic\nArguments nil {A}%_type_scope\nExpands to: Constructor Corelib.Init.Datatypes.nil\nDeclared in library Corelib.Init.Datatypes, line 310, characters 3-6"}
  {"id":2,"jsonrpc":"2.0","error":{"code":-32803,"message":"the query had no \"notice\" feedback at that index"}}
  {"id":3,"jsonrpc":"2.0","error":{"code":-32803,"message":"the query result does not contain valid JSON"}}

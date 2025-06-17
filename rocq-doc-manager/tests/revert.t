  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v <<EOF
  > Definition test := nat.
  > About nat.
  > Check test.
  > EOF

  $ cat > calls.txt <<EOF
  > load_file
  > doc_suffix
  > run_step
  > run_step
  > run_step
  > revert_before [false,2]
  > revert_before [true,0]
  > doc_prefix
  > doc_suffix
  > run_step
  > run_step
  > run_step
  > EOF

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap > commands.txt

  $ cat commands.txt | rocq-doc-manager -Q . test.dir test.v | jsonrpc-tp.tp_unwrap
  {"id":1,"jsonrpc":"2.0","result":null}
  {"id":2,"jsonrpc":"2.0","result":[{"kind":"command","text":"Definition test := nat."},{"kind":"blanks","text":"\n"},{"kind":"command","text":"About nat."},{"kind":"blanks","text":"\n"},{"kind":"command","text":"Check test."}]}
  {"id":3,"jsonrpc":"2.0","result":{"open_subgoals":null,"new_constants":["test.dir.test.test"]}}
  {"id":4,"jsonrpc":"2.0","result":null}
  {"id":5,"jsonrpc":"2.0","result":{"open_subgoals":null}}
  {"id":6,"jsonrpc":"2.0","result":null}
  {"id":7,"jsonrpc":"2.0","result":null}
  {"id":8,"jsonrpc":"2.0","result":[]}
  {"id":9,"jsonrpc":"2.0","result":[{"kind":"command","text":"About nat."},{"kind":"blanks","text":"\n"},{"kind":"command","text":"Check test."}]}
  {"id":10,"jsonrpc":"2.0","result":{"open_subgoals":null}}
  {"id":11,"jsonrpc":"2.0","result":null}
  {"id":12,"jsonrpc":"2.0","error":{"data":{"loc":{"fname":["ToplevelInput"],"line_nb":1,"bol_pos":0,"line_nb_last":1,"bol_pos_last":0,"bp":51,"ep":55}},"code":-32803,"message":"The reference test was not found in the current environment."}}

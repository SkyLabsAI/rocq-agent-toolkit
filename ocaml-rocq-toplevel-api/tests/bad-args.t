  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ rocq-toplevel-api.tester -not-a-valid-arg
  Don't know what to do with -not-a-valid-arg
  See -help for the list of supported options
  Error: the toplevel process failed to start (exited with code 1).
  [1]

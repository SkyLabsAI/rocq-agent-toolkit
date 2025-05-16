  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ coqc test.v
  No available derivers.
  File "./test.v", line 10, characters 0-32:
  Error: deriver pp does not exist.
  
  [1]

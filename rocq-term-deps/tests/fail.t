  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v <<EOF
  > Require Import skylabs_ai.tools.term_deps.plugin.
  > DepsOf nat.
  > EOF

  $ coqc test.v
  File "./test.v", line 2, characters 7-10:
  Error: This reference is not a constant, but an inductive.
  
  [1]

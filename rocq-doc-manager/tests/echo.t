  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v <<EOF
  > Require Import Stdlib.ZArith.BinInt.
  > 
  > About nil.
  >     Definition junk :=
  > 
  > 
  > nat.
  > Check 12 < 42 <= 100.
  > 
  > 
  > Theorem test : forall x : nat, x = x.
  > Proof.
  >   intro x.
  >   reflexivity.
  > Qed.
  > 
  > 
  > EOF

  $ cp test.v test.v.orig
  $ cat > calls.txt <<EOF
  > load_file [0]
  > commit [0,null,false,true]
  > EOF

  $ cat calls.txt | jsonrpc-tp.build_requests | jsonrpc-tp.tp_wrap > commands.txt

  $ cat commands.txt | rocq-doc-manager test.v -- -Q . test.dir | jsonrpc-tp.tp_unwrap
  { "method": "ready_seq", "jsonrpc": "2.0" }
  { "id": 1, "jsonrpc": "2.0", "result": null }
  { "id": 2, "jsonrpc": "2.0", "result": null }

  $ diff test.v test.v.orig

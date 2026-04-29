  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled


  $ mkdir subdir
  $ cat > subdir/test.v <<EOF
  > (* Test file. *)
  > Theorem test : forall x : nat, x = x.
  > Proof.
  >   intro x.
  >   reflexivity.
  > Qed.
  > 
  > (* END *)
  > EOF

  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF

  $ cat > dune <<EOF
  > (include_subdirs qualified)
  > (rocq.theory
  >  (name test))
  > EOF

  $ ls -alR .
  $ rocq-ed init subdir/test.v
  $ rocq-ed status subdir/test.v
  $ rocq-ed stop subdir/test.v
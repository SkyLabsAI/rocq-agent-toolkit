  $ export DUNE_ROOT=$PWD

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

  $ mkdir subdir/subsubdir
  $ cp subdir/test.v subdir/subsubdir/test.v

  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF

  $ cat > dune <<EOF
  > (include_subdirs qualified)
  > (rocq.theory
  >  (name text))
  > EOF

  $ eval $(rocq-ed init subdir/test.v)
  $ rocq-ed status
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
     4|   intro x.
     5|   reflexivity.
     6| Qed.
  $ cd subdir
  $ rocq-ed stop

  $ eval $(rocq-ed init subsubdir/test.v)
  $ rocq-ed status
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
     4|   intro x.
     5|   reflexivity.
     6| Qed.
  $ rocq-ed stop

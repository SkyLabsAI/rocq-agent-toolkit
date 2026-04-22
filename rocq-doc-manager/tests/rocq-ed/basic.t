  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ cat > test.v <<EOF
  > (* Test file. *)
  > Theorem test : forall x : nat, x = x.
  > Proof.
  >   intro x.
  >   reflexivity.
  > Qed.
  > 
  > (* END *)
  > EOF

  $ # Testing that failures during `rocq-ed init` do not break future `rocq-ed init` attempts.
  $ rocq-ed init test.v
  Error: Cannot find file: test.v
  Hint: Is the file part of a stanza?
  Hint: Has the file been written to disk?
  Error: cannot get CLI arguments for "test.v" (process exited with code 1).
  [1]

  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF

  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF

  $ rocq-ed init test.v
  Warning: Clearning up stale directory test.v.rocqed
  $ find test.v.rocqed | LC_ALL=C sort
  test.v.rocqed
  test.v.rocqed/daemon.pid
  test.v.rocqed/log
  test.v.rocqed/req.fifo
  test.v.rocqed/res.fifo
  $ rocq-ed status test.v
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
     4|   intro x.
     5|   reflexivity.
     6| Qed.
     7| 
     8| (* END *)
  $ rocq-ed status -C 0 test.v
     1| <CURSOR>(* Test file. *)
  $ rocq-ed status -C 1 test.v
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
  $ rocq-ed status -C 2 test.v
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
  $ rocq-ed steps --count 5 test.v
  $ rocq-ed status test.v
     1| (* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
     4|   <CURSOR>intro x.
     5|   reflexivity.
     6| Qed.
     7| 
     8| (* END *)
  $ rocq-ed undo --count 5 test.v
  $ rocq-ed status test.v
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
     4|   intro x.
     5|   reflexivity.
     6| Qed.
     7| 
     8| (* END *)
  $ rocq-ed steps --count 5 test.v
  $ rocq-ed status -C 0 test.v
     4|   <CURSOR>intro x.
  $ rocq-ed status -C 1 test.v
     3| Proof.
     4|   <CURSOR>intro x.
     5|   reflexivity.
  $ rocq-ed status -C 2 test.v
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
     4|   <CURSOR>intro x.
     5|   reflexivity.
     6| Qed.
  $ rocq-ed steps --count 3 test.v
  $ rocq-ed status test.v
     1| (* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
     4|   intro x.
     5|   reflexivity.<CURSOR>
     6| Qed.
     7| 
     8| (* END *)
  $ rocq-ed steps --count 3 test.v
  $ rocq-ed status test.v
     1| (* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
     4|   intro x.
     5|   reflexivity.
     6| Qed.
     7| 
     8| (* END *)
     9| <CURSOR>
  $ rocq-ed stop test.v
  $ find test.v.rocq-ed
  find: 'test.v.rocq-ed': No such file or directory
  [1]

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

  $ eval $(rocq-ed init test.v)
  Error: Cannot find file: test.v
  Hint: Is the file part of a stanza?
  Hint: Has the file been written to disk?
  Error: cannot get CLI arguments for "test.v" (process exited with code 1).
  [1]

  $ rocq-ed status
  rocq-ed: environment variable ROCQED_SESSION_ID is undefined, so the
           --session-id option is required
  [124]

  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF

  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF

  $ printenv ROCQED_SESSION_ID
  [1]
  $ find "$HOME" | sort
  $TESTCASE_ROOT/user

  $ eval $(rocq-ed init test.v)

  $ find "$HOME" | sed "s/$(printenv ROCQED_SESSION_ID)/xxxxxx/" | sort
  $TESTCASE_ROOT/user
  $TESTCASE_ROOT/user/.cache
  $TESTCASE_ROOT/user/.cache/rocq-ed
  $TESTCASE_ROOT/user/.cache/rocq-ed/xxxxxx
  $TESTCASE_ROOT/user/.cache/rocq-ed/xxxxxx/client.lock
  $TESTCASE_ROOT/user/.cache/rocq-ed/xxxxxx/log
  $TESTCASE_ROOT/user/.cache/rocq-ed/xxxxxx/pid
  $TESTCASE_ROOT/user/.cache/rocq-ed/xxxxxx/server.lock
  $TESTCASE_ROOT/user/.cache/rocq-ed/xxxxxx/socket

  $ rocq-ed status
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
     4|   intro x.
     5|   reflexivity.
     6| Qed.
  $ rocq-ed status --context-lines 0
     1| <CURSOR>(* Test file. *)
  $ rocq-ed status --context-lines 1
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
  $ rocq-ed status --context-lines 2
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
  $ rocq-ed status --context-lines all
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
     4|   intro x.
     5|   reflexivity.
     6| Qed.
     7| 
     8| (* END *)
  $ rocq-ed move --print-context --print-goals --item=+5
     1| (* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
     4|   <CURSOR>intro x.
     5|   reflexivity.
     6| Qed.
     7| 
     8| (* END *)
  
  Goal 1:
    ============================
    forall x : nat, x = x
  $ rocq-ed status
     1| (* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
     4|   <CURSOR>intro x.
     5|   reflexivity.
     6| Qed.
     7| 
     8| (* END *)
  $ rocq-ed move --print-context --print-goals --item=-5
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
     4|   intro x.
     5|   reflexivity.
     6| Qed.
  
  Not currently in a proof.
  $ rocq-ed status
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
     4|   intro x.
     5|   reflexivity.
     6| Qed.
  $ rocq-ed move --print-context --print-goals --item=+5
     1| (* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
     4|   <CURSOR>intro x.
     5|   reflexivity.
     6| Qed.
     7| 
     8| (* END *)
  
  Goal 1:
    ============================
    forall x : nat, x = x
  $ rocq-ed status --context-lines 0
     4|   <CURSOR>intro x.
  $ rocq-ed status --context-lines 1
     3| Proof.
     4|   <CURSOR>intro x.
     5|   reflexivity.
  $ rocq-ed status --context-lines 2
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
     4|   <CURSOR>intro x.
     5|   reflexivity.
     6| Qed.
  $ rocq-ed move --print-context --print-goals --item=+3
     1| (* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
     4|   intro x.
     5|   reflexivity.<CURSOR>
     6| Qed.
     7| 
     8| (* END *)
  
  No open goals.
  $ rocq-ed status
     1| (* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
     4|   intro x.
     5|   reflexivity.<CURSOR>
     6| Qed.
     7| 
     8| (* END *)
  $ rocq-ed move --print-context --print-goals --item=+3
     4|   intro x.
     5|   reflexivity.
     6| Qed.
     7| 
     8| (* END *)
     9| <CURSOR>
  
  Not currently in a proof.
  $ rocq-ed status
     4|   intro x.
     5|   reflexivity.
     6| Qed.
     7| 
     8| (* END *)
     9| <CURSOR>
  $ rocq-ed move --print-context --print-goals --item=+100
     4|   intro x.
     5|   reflexivity.
     6| Qed.
     7| 
     8| (* END *)
     9| <CURSOR>
  
  Not currently in a proof.
  
  Warning: moved forward by 0 of 100 requested items; reached the end of the document.
  $ rocq-ed move --print-context --print-goals --item=-100
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof.
     4|   intro x.
     5|   reflexivity.
     6| Qed.
  
  Not currently in a proof.
  
  Warning: moved backward by 11 of 100 requested items; reached the start of the document.
  $ rocq-ed stop

  $ find "$HOME" | sed "s/$(printenv ROCQED_SESSION_ID)/xxxxxx/" | sort
  $TESTCASE_ROOT/user
  $TESTCASE_ROOT/user/.cache
  $TESTCASE_ROOT/user/.cache/rocq-ed

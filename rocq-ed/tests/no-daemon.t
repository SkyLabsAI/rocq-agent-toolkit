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

  $ rocq-ed init --no-daemon test.v
  Error: Cannot find file: test.v
  Hint: Is the file part of a stanza?
  Hint: Has the file been written to disk?
  Error: cannot get CLI arguments for "test.v" (process exited with code 1).
  [1]
  $ printenv ROCQED_SESSION_ID
  [1]
  $ find "$HOME" | sort
  $TESTCASE_ROOT/user

  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF

  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF

  $ rocq-ed init --no-daemon test.v > log 2>&1 &
  $ until grep ROCQED_SESSION_ID log > /dev/null; do sleep 0.05; done
  $ export $(grep ROCQED_SESSION_ID log)

  $ find "$HOME" | sed "s/$(printenv ROCQED_SESSION_ID)/xxxxxx/" | sort
  $TESTCASE_ROOT/user
  $TESTCASE_ROOT/user/.cache
  $TESTCASE_ROOT/user/.cache/rocq-ed
  $TESTCASE_ROOT/user/.cache/rocq-ed/xxxxxx
  $TESTCASE_ROOT/user/.cache/rocq-ed/xxxxxx/client.lock
  $TESTCASE_ROOT/user/.cache/rocq-ed/xxxxxx/pid
  $TESTCASE_ROOT/user/.cache/rocq-ed/xxxxxx/server.lock
  $TESTCASE_ROOT/user/.cache/rocq-ed/xxxxxx/socket

  $ rocq-ed status --context-lines 0
     1| <CURSOR>(* Test file. *)
  $ rocq-ed steps --count-items 2
  $ rocq-ed status --context-lines 0
     2| Theorem test : forall x : nat, x = x.<CURSOR>
  $ rocq-ed stop

  $ find "$HOME" | sed "s/$(printenv ROCQED_SESSION_ID)/xxxxxx/" | sort
  $TESTCASE_ROOT/user
  $TESTCASE_ROOT/user/.cache
  $TESTCASE_ROOT/user/.cache/rocq-ed

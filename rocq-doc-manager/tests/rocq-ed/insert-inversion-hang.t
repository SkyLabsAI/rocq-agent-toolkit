  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ cat > test.v <<EOF
  > Theorem test : False -> True /\ True.
  > Proof.
  >   intros H; split.
  > EOF

  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF

  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF

  $ timeout 5s rocq-ed init test.v
  $ timeout 5s rocq-ed steps --count-items=all test.v
     1| Theorem test : False -> True /\ True.
     2| Proof.
     3|   intros H; split.
     4| <CURSOR>
  
  Goal 1:
    H : False
    ============================
    True
  
  Goal 2:
    H : False
    ============================
    True
  
  $ timeout 5s rocq-ed insert --text="*inversion H." test.v
     1| Theorem test : False -> True /\ True.
     2| Proof.
     3|   intros H; split.
     4| *inversion H.<CURSOR>
  
  Unfocused goals: 1
  $ timeout 5s rocq-ed backwards --count-items=1 test.v
     1| Theorem test : False -> True /\ True.
     2| Proof.
     3|   intros H; split.
     4| *<CURSOR>inversion H.
  
  Goal 1:
    H : False
    ============================
    True
  
  Unfocused goals: 1
  $ timeout 5s rocq-ed delete --count-items=1 test.v
     1| Theorem test : False -> True /\ True.
     2| Proof.
     3|   intros H; split.
     4| *<CURSOR>
  
  Goal 1:
    H : False
    ============================
    True
  
  Unfocused goals: 1

The next insertion leaves the daemon stuck.  Use a short timeout so the test
case does not wait indefinitely.

  $ timeout 5s rocq-ed insert --text="*inversion H." test.v
  [124]

After removing the stale client lock left by the timed-out client, even a status
request gets no daemon response.

  $ rmdir .test.v.rocqed/client.lock 2>/dev/null || true
  $ timeout 5s rocq-ed status test.v
  [124]

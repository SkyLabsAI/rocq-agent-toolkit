  $ cat > test.v <<EOF
  > Theorem test : forall x : nat, x = x.
  > Proof.
  >   intro x.
  >   reflexivity.
  > Qed.
  > EOF
  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF
  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF

  $ SESSION1=$(rocq-ed init test.v | sed 's/^[^=]*=//')
  $ SESSION2=$(rocq-ed init test.v | sed 's/^[^=]*=//')

  $ rocq-ed steps --count-items=2 --session-id=${SESSION1}
  $ rocq-ed status --context-lines=0 --session-id=${SESSION1}
     2| <CURSOR>Proof.
  $ rocq-ed status --context-lines=0 --session-id=${SESSION2}
     1| <CURSOR>Theorem test : forall x : nat, x = x.

  $ rocq-ed stop --session-id=${SESSION1}
  $ rocq-ed stop --session-id=${SESSION2}

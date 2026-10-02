`try` processes a candidate at the cursor, prints the resulting proof state, and
rolls the document back: nothing is inserted, whether the candidate works or not.

  $ cat > test.v <<EOF
  > Theorem test : forall x : nat, True /\ x = x.
  > Proof.
  > Admitted.
  > EOF

  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF

  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF

  $ eval $(rocq-ed init test.v)
  $ rocq-ed steps --count-items 3
  $ rocq-ed insert --keep=none --print-goals --text $'\n  intros x; split.\n'
  Open goals after the inserted text (prior to document rollback):
  
  Goal 1:
    x : nat
    ============================
    True
  
  Goal 2:
    x : nat
    ============================
    x = x
  $ rocq-ed status
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.<CURSOR>
     3| Admitted.
  $ rocq-ed insert --keep=none --print-goals --text $'\n  reflexivity.\n'
  Open goals before the failing suffix (prior to document rollback):
  
  Goal 1:
    ============================
    forall x : nat, True /\ x = x
  
  The document is unchanged.
  
  Error: could not process suffix "reflexivity.\n".
   The relation and is not a declared reflexive relation. Maybe you need to require the Corelib.Classes.RelationClasses library
  [1]
  $ rocq-ed goals
  Goal 1:
    ============================
    forall x : nat, True /\ x = x
  $ rocq-ed insert --text $'\n  intros x; split.\n'
  $ rocq-ed status
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.
     3|   intros x; split.
     4| <CURSOR>
     5| Admitted.
  $ rocq-ed stop

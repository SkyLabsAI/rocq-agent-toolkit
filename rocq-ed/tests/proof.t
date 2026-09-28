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
  $ rocq-ed goals
  Not currently in a proof.
  $ rocq-ed steps --print-context --print-goals --count-items 3
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.<CURSOR>
     3| Admitted.
  
  Goal 1:
    ============================
    forall x : nat, True /\ x = x
  
  $ rocq-ed status
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.<CURSOR>
     3| Admitted.
  $ rocq-ed goals
  Goal 1:
    ============================
    forall x : nat, True /\ x = x
  
  $ rocq-ed steps --print-goals --count-items 0
  Goal 1:
    ============================
    forall x : nat, True /\ x = x
  
  $ rocq-ed insert --print-context --print-goals --text $'\n  intros x; split.'
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.
     3|   intros x; split.<CURSOR>
     4| Admitted.
  
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
     2| Proof.
     3|   intros x; split.<CURSOR>
     4| Admitted.
  $ rocq-ed goals
  Goal 1:
    x : nat
    ============================
    True
  
  Goal 2:
    x : nat
    ============================
    x = x
  
  $ rocq-ed insert --print-context --print-goals --text $'\n  - fail.\n  -'
  Error: could not process suffix "fail.\n  -".
  Tactic failure.
  The document is unchanged.
  [1]
  $ rocq-ed status
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.
     3|   intros x; split.<CURSOR>
     4| Admitted.
  $ rocq-ed insert --print-context --print-goals --text $'\n  - constructor.\n  - '
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.
     3|   intros x; split.
     4|   - constructor.
     5|   - <CURSOR>
     6| Admitted.
  
  Goal 1:
    x : nat
    ============================
    x = x
  
  $ rocq-ed status
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.
     3|   intros x; split.
     4|   - constructor.
     5|   - <CURSOR>
     6| Admitted.
  $ rocq-ed query --text "About eq_refl."
  eq_refl : forall {A : Type} {x : A}, x = x
  
  eq_refl is template universe polymorphic
  Arguments eq_refl {A}%_type_scope {x}, [_] _
  Expands to: Constructor Corelib.Init.Logic.eq_refl
  Declared in library Corelib.Init.Logic, line 380, characters 4-11
  $ rocq-ed status
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.
     3|   intros x; split.
     4|   - constructor.
     5|   - <CURSOR>
     6| Admitted.

Test that the output of queries is properly terminated by a newline

  $ rocq-ed query --text "Show." && echo "<NEWLINE>"
  1 goal
    
    x : nat
    ============================
    x = x
  <NEWLINE>
  $ rocq-ed insert --print-context --print-goals --text "reflexivity."
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.
     3|   intros x; split.
     4|   - constructor.
     5|   - reflexivity.<CURSOR>
     6| Admitted.
  
  $ rocq-ed status
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.
     3|   intros x; split.
     4|   - constructor.
     5|   - reflexivity.<CURSOR>
     6| Admitted.
  $ rocq-ed steps --print-context --print-goals --count-items 2
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.
     3|   intros x; split.
     4|   - constructor.
     5|   - reflexivity.
     6| Admitted.<CURSOR>
  
  Not currently in a proof.
  $ rocq-ed status
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.
     3|   intros x; split.
     4|   - constructor.
     5|   - reflexivity.
     6| Admitted.<CURSOR>
  $ cat test.v
  Theorem test : forall x : nat, True /\ x = x.
  Proof.
  Admitted.
  $ rocq-ed commit
  $ cat test.v
  Theorem test : forall x : nat, True /\ x = x.
  Proof.
    intros x; split.
    - constructor.
    - reflexivity.
  Admitted.
  $ rocq-ed insert --print-context --print-goals --text $'\n\nGoal True /\ True.\nProof.\n  split.'
     5|   - reflexivity.
     6| Admitted.
     7| 
     8| Goal True /\ True.
     9| Proof.
    10|   split.<CURSOR>
  
  Goal 1:
    ============================
    True
  
  Goal 2:
    ============================
    True
  
  $ rocq-ed insert --print-context --print-goals --text $' 1: shelve.'
     5|   - reflexivity.
     6| Admitted.
     7| 
     8| Goal True /\ True.
     9| Proof.
    10|   split. 1: shelve.<CURSOR>
  
  Goal 1:
    ============================
    True
  
  Shelved goals: 1
  $ rocq-ed status
     5|   - reflexivity.
     6| Admitted.
     7| 
     8| Goal True /\ True.
     9| Proof.
    10|   split. 1: shelve.<CURSOR>
  $ rocq-ed goals
  Goal 1:
    ============================
    True
  
  Shelved goals: 1
  $ rocq-ed insert --print-context --print-goals --keep=all --text $'\n  fail.'
  Error: could not process suffix "fail.".
  Tactic failure.
  [1]
  $ rocq-ed status --context-lines 3
     8| Goal True /\ True.
     9| Proof.
    10|   split. 1: shelve.
    11|   <CURSOR>fail.
  $ rocq-ed stop

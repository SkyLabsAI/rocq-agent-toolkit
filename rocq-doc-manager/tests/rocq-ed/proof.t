  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

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

  $ rocq-ed init test.v
  $ rocq-ed goals test.v
  Not currently in a proof.
  $ rocq-ed steps --count 3 test.v
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.<CURSOR>
     3| Admitted.
  
  Goal 1:
    ============================
    forall x : nat, True /\ x = x
  
  $ rocq-ed status test.v
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.<CURSOR>
     3| Admitted.
  $ rocq-ed goals test.v
  Goal 1:
    ============================
    forall x : nat, True /\ x = x
  
  $ rocq-ed insert --text $'\n  intros x; split.' test.v
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
  
  $ rocq-ed status test.v
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.
     3|   intros x; split.<CURSOR>
     4| Admitted.
  $ rocq-ed goals test.v
  Goal 1:
    x : nat
    ============================
    True
  
  Goal 2:
    x : nat
    ============================
    x = x
  
  $ rocq-ed insert --text $'\n  - fail.\n  -' test.v
  Error: could not process suffix "fail.\n  -".
  Tactic failure.
  [1]
  $ rocq-ed status test.v
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.
     3|   intros x; split.
     4|   - <CURSOR>
     5| Admitted.
  $ rocq-ed insert --text $'constructor.\n  - ' test.v
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
  
  $ rocq-ed status test.v
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.
     3|   intros x; split.
     4|   - constructor.
     5|   - <CURSOR>
     6| Admitted.
  $ rocq-ed query --text "About eq_refl." test.v
  eq_refl : forall {A : Type} {x : A}, x = x
  
  eq_refl is template universe polymorphic
  Arguments eq_refl {A}%_type_scope {x}, [_] _
  Expands to: Constructor Corelib.Init.Logic.eq_refl
  Declared in library Corelib.Init.Logic, line 379, characters 4-11
  $ rocq-ed status test.v
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.
     3|   intros x; split.
     4|   - constructor.
     5|   - <CURSOR>
     6| Admitted.
  $ # Test that the output of queries is properly terminated by a newline
  $ rocq-ed query --text "Show." test.v && echo "<NEWLINE>"
  1 goal
    
    x : nat
    ============================
    x = x
  <NEWLINE>
  $ rocq-ed insert --text "reflexivity." test.v
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.
     3|   intros x; split.
     4|   - constructor.
     5|   - reflexivity.<CURSOR>
     6| Admitted.
  
  $ rocq-ed status test.v
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.
     3|   intros x; split.
     4|   - constructor.
     5|   - reflexivity.<CURSOR>
     6| Admitted.
  $ rocq-ed steps --count 2 test.v
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.
     3|   intros x; split.
     4|   - constructor.
     5|   - reflexivity.
     6| Admitted.<CURSOR>
  
  Not currently in a proof.
  $ rocq-ed status test.v
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
  $ rocq-ed commit test.v
  $ cat test.v
  Theorem test : forall x : nat, True /\ x = x.
  Proof.
    intros x; split.
    - constructor.
    - reflexivity.
  Admitted.
  $ rocq-ed insert --text $'\n\nGoal True /\ True.\nProof.\n  split.' test.v
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
  
  $ rocq-ed insert --text $' 1: shelve.' test.v
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
  $ rocq-ed status test.v
     1| Theorem test : forall x : nat, True /\ x = x.
     2| Proof.
     3|   intros x; split.
     4|   - constructor.
     5|   - reflexivity.
     6| Admitted.
     7| 
     8| Goal True /\ True.
     9| Proof.
    10|   split. 1: shelve.<CURSOR>
  $ rocq-ed goals test.v
  Goal 1:
    ============================
    True
  
  Shelved goals: 1
  $ rocq-ed stop test.v

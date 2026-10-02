  $ cat > test.v <<EOF
  > Require Import Init.Datatypes.
  > Theorem add_1_n : forall n : nat, S n + n = S (n + n).
  > Proof.
  >   intros n.
  >   (* TODO: implement this *)
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
  $ rocq-ed move --print-context --print-goals --item=+7
     1| Require Import Init.Datatypes.
     2| Theorem add_1_n : forall n : nat, S n + n = S (n + n).
     3| Proof.
     4|   intros n.<CURSOR>
     5|   (* TODO: implement this *)
  
  Goal 1:
    n : nat
    ============================
    S n + n = S (n + n)
  $ rocq-ed status
     1| Require Import Init.Datatypes.
     2| Theorem add_1_n : forall n : nat, S n + n = S (n + n).
     3| Proof.
     4|   intros n.<CURSOR>
     5|   (* TODO: implement this *)
  $ rocq-ed delete --print-context --print-goals --count-items=1
     1| Require Import Init.Datatypes.
     2| Theorem add_1_n : forall n : nat, S n + n = S (n + n).
     3| Proof.
     4|   intros n.<CURSOR>
  
  Goal 1:
    n : nat
    ============================
    S n + n = S (n + n)
  $ rocq-ed insert --print-context --print-goals --text="reflexivity. Qed."
  The document is unchanged.
  
  Error: could not process suffix "reflexivity. Qed.".
  leading blanks required at this point in the document
  [1]
  $ rocq-ed insert --print-context --print-goals --text=" reflexivity. Qed."
     1| Require Import Init.Datatypes.
     2| Theorem add_1_n : forall n : nat, S n + n = S (n + n).
     3| Proof.
     4|   intros n. reflexivity. Qed.<CURSOR>
  
  Not currently in a proof.
  $ rocq-ed status
     1| Require Import Init.Datatypes.
     2| Theorem add_1_n : forall n : nat, S n + n = S (n + n).
     3| Proof.
     4|   intros n. reflexivity. Qed.<CURSOR>
  $ rocq-ed goals
  Not currently in a proof.

  $ rocq-ed stop

  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

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

  $ rocq-ed init test.v
  $ rocq-ed steps --count=7 test.v
     1| Require Import Init.Datatypes.
     2| Theorem add_1_n : forall n : nat, S n + n = S (n + n).
     3| Proof.
     4|   intros n.<CURSOR>
     5|   (* TODO: implement this *)
  
  Goal 1:
    n : nat
    ============================
    S n + n = S (n + n)
  
  $ rocq-ed status test.v
     1| Require Import Init.Datatypes.
     2| Theorem add_1_n : forall n : nat, S n + n = S (n + n).
     3| Proof.
     4|   intros n.<CURSOR>
     5|   (* TODO: implement this *)
  $ rocq-ed delete --count=1 test.v
     1| Require Import Init.Datatypes.
     2| Theorem add_1_n : forall n : nat, S n + n = S (n + n).
     3| Proof.
     4|   intros n.<CURSOR>
  
  Goal 1:
    n : nat
    ============================
    S n + n = S (n + n)
  
  $ rocq-ed insert --text="reflexivity. Qed." test.v
  Error: could not process suffix "reflexivity. Qed.".
  leading blanks required at this point in the document
  [1]
  $ rocq-ed insert --text=" reflexivity. Qed." test.v
     1| Require Import Init.Datatypes.
     2| Theorem add_1_n : forall n : nat, S n + n = S (n + n).
     3| Proof.
     4|   intros n. reflexivity. Qed.<CURSOR>
  
  Not currently in a proof.
  $ rocq-ed status test.v
     1| Require Import Init.Datatypes.
     2| Theorem add_1_n : forall n : nat, S n + n = S (n + n).
     3| Proof.
     4|   intros n. reflexivity. Qed.<CURSOR>
  $ rocq-ed goals test.v
  Not currently in a proof.

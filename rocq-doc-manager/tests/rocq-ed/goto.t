  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ export TERM=dumb

  $ cat > test.v <<EOF
  > (* Test file. *)
  > Theorem test : forall x : nat, x = x.
  > Proof. intro x. reflexivity. Qed.
  > 
  > (* END *)
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
  $ rocq-ed goto --position-line-column 0 test.v
  Usage: rocq-ed goto [--help] --position-line-column=LINE[:COLUMN]
         [--print-context[=NUM]] [--print-goals] [OPTION]… FILE
  rocq-ed: option '--position-line-column': The line number should be at least
           1.
  [124]
  $ rocq-ed goto --position-line-column 0:1 test.v
  Usage: rocq-ed goto [--help] --position-line-column=LINE[:COLUMN]
         [--print-context[=NUM]] [--print-goals] [OPTION]… FILE
  rocq-ed: option '--position-line-column': The line number should be at least
           1.
  [124]
  $ rocq-ed goto --position-line-column 1:0 test.v
  Usage: rocq-ed goto [--help] --position-line-column=LINE[:COLUMN]
         [--print-context[=NUM]] [--print-goals] [OPTION]… FILE
  rocq-ed: option '--position-line-column': The column number should be at
           least 1.
  [124]
  $ rocq-ed goto --print-context --print-goals --position-line-column 6:1 test.v
  Error: no item on the given line.
  The cursor is now at index 0.
  [1]
  $ rocq-ed goto --print-context --print-goals --position-line-column 1:18 test.v
  Error: no item on the given column.
  The cursor is now at index 0.
  [1]
  $ rocq-ed goto --print-context --print-goals --position-line-column 1:1 test.v
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof. intro x. reflexivity. Qed.
     4| 
     5| (* END *)
  
  Not currently in a proof.
  $ rocq-ed status test.v
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof. intro x. reflexivity. Qed.
     4| 
     5| (* END *)
  $ rocq-ed goto --print-context --print-goals --position-line-column 1:17 test.v
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof. intro x. reflexivity. Qed.
     4| 
     5| (* END *)
  
  Not currently in a proof.
  $ rocq-ed status test.v
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof. intro x. reflexivity. Qed.
     4| 
     5| (* END *)
  $ rocq-ed goto --print-context --print-goals --position-line-column 2:1 test.v
     1| (* Test file. *)
     2| <CURSOR>Theorem test : forall x : nat, x = x.
     3| Proof. intro x. reflexivity. Qed.
     4| 
     5| (* END *)
  
  Not currently in a proof.
  $ rocq-ed status test.v
     1| (* Test file. *)
     2| <CURSOR>Theorem test : forall x : nat, x = x.
     3| Proof. intro x. reflexivity. Qed.
     4| 
     5| (* END *)
  $ rocq-ed goto --print-context --print-goals --position-line-column 3:1 test.v
     1| (* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| <CURSOR>Proof. intro x. reflexivity. Qed.
     4| 
     5| (* END *)
  
  Goal 1:
    ============================
    forall x : nat, x = x
  
  $ rocq-ed status test.v
     1| (* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| <CURSOR>Proof. intro x. reflexivity. Qed.
     4| 
     5| (* END *)
  $ rocq-ed goto --print-context --print-goals --position-line-column 3:8 test.v
     1| (* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof. <CURSOR>intro x. reflexivity. Qed.
     4| 
     5| (* END *)
  
  Goal 1:
    ============================
    forall x : nat, x = x
  
  $ rocq-ed status test.v
     1| (* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof. <CURSOR>intro x. reflexivity. Qed.
     4| 
     5| (* END *)
  $ rocq-ed goto --print-context --print-goals --position-line-column 3:34 test.v
     1| (* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof. intro x. reflexivity. Qed.<CURSOR>
     4| 
     5| (* END *)
  
  Not currently in a proof.
  $ rocq-ed status test.v
     1| (* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof. intro x. reflexivity. Qed.<CURSOR>
     4| 
     5| (* END *)
  $ rocq-ed stop test.v

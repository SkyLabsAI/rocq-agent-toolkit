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

  $ eval $(rocq-ed init test.v)
  $ rocq-ed goto --position-line-column 0
  Usage: rocq-ed goto [--help] [OPTION]…
  rocq-ed: option '--position-line-column': The line number should be at least
           1.
  [124]
  $ rocq-ed goto --position-line-column 0:1
  Usage: rocq-ed goto [--help] [OPTION]…
  rocq-ed: option '--position-line-column': The line number should be at least
           1.
  [124]
  $ rocq-ed goto --position-line-column 1:0
  Usage: rocq-ed goto [--help] [OPTION]…
  rocq-ed: option '--position-line-column': The column number should be at
           least 1.
  [124]
  $ rocq-ed goto --print-context --print-goals --position-line-column 6:1
  Error: no item on line 6.
  [1]
  $ rocq-ed goto --print-context --print-goals --position-line-column 1:18
  Error: no item on line 1, column 18.
  [1]
  $ rocq-ed goto --print-context --print-goals --position-line-column 1:1
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof. intro x. reflexivity. Qed.
     4| 
     5| (* END *)
  
  Not currently in a proof.
  $ rocq-ed status
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof. intro x. reflexivity. Qed.
     4| 
     5| (* END *)
  $ rocq-ed goto --print-context --print-goals --position-line-column 1:17
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof. intro x. reflexivity. Qed.
     4| 
     5| (* END *)
  
  Not currently in a proof.
  $ rocq-ed status
     1| <CURSOR>(* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof. intro x. reflexivity. Qed.
     4| 
     5| (* END *)
  $ rocq-ed goto --print-context --print-goals --position-line-column 2:1
     1| (* Test file. *)
     2| <CURSOR>Theorem test : forall x : nat, x = x.
     3| Proof. intro x. reflexivity. Qed.
     4| 
     5| (* END *)
  
  Not currently in a proof.
  $ rocq-ed status
     1| (* Test file. *)
     2| <CURSOR>Theorem test : forall x : nat, x = x.
     3| Proof. intro x. reflexivity. Qed.
     4| 
     5| (* END *)
  $ rocq-ed goto --print-context --print-goals --position-line-column 3:1
     1| (* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| <CURSOR>Proof. intro x. reflexivity. Qed.
     4| 
     5| (* END *)
  
  Goal 1:
    ============================
    forall x : nat, x = x
  
  $ rocq-ed status
     1| (* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| <CURSOR>Proof. intro x. reflexivity. Qed.
     4| 
     5| (* END *)
  $ rocq-ed goto --print-context --print-goals --position-line-column 3:8
     1| (* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof. <CURSOR>intro x. reflexivity. Qed.
     4| 
     5| (* END *)
  
  Goal 1:
    ============================
    forall x : nat, x = x
  
  $ rocq-ed status
     1| (* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof. <CURSOR>intro x. reflexivity. Qed.
     4| 
     5| (* END *)
  $ rocq-ed goto --print-context --print-goals --position-line-column 3:34
     1| (* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof. intro x. reflexivity. Qed.<CURSOR>
     4| 
     5| (* END *)
  
  Not currently in a proof.
  $ rocq-ed status
     1| (* Test file. *)
     2| Theorem test : forall x : nat, x = x.
     3| Proof. intro x. reflexivity. Qed.<CURSOR>
     4| 
     5| (* END *)
  $ rocq-ed stop

  $ cat > failure.v <<EOF
  > Check nat.
  > Check missing_identifier.
  > (* END *)
  > EOF

  $ eval $(rocq-ed init failure.v)
  $ rocq-ed goto --position-line-column 3:1
  Error: failed to process the item at line 2, column 1.
  The reference missing_identifier was not found in the current environment.
  [1]
  $ rocq-ed goto --position-line-column 3:1
  Error: failed to process the item at line 2, column 1.
  The reference missing_identifier was not found in the current environment.
  [1]
  $ rocq-ed stop

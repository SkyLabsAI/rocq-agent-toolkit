  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF

  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF

  $ cat > test.v <<EOF
  > Definition Lookup (K A M : Type) := K -> M -> option A.
  > Fixpoint get {A} : Lookup nat A (list A) :=
  >   fun k xs => match xs with
  >   | nil => None
  >   | cons x xs => match k with O => Some x | S k => get k xs end
  >   end.
  > Lemma t (k : nat) (l : list nat) : get k l = None.
  > Proof.
  > Admitted.
  > EOF

  $ eval $(rocq-ed init test.v)
  $ rocq-ed move -p 8:7
  $ rocq-ed insert --text=' unfold get. '
  The document is unchanged.
  
  Error: could not parse or process remaining text "unfold get. ".
  Anomaly "Uncaught exception Failure("nth")."
  Please report at http://rocq-prover.org/bugs/.
  [1]
  $ rocq-ed status
     3|   fun k xs => match xs with
     4|   | nil => None
     5|   | cons x xs => match k with O => Some x | S k => get k xs end
     6|   end.
     7| Lemma t (k : nat) (l : list nat) : get k l = None.
     8| Proof.<CURSOR>
     9| Admitted.
  $ rocq-ed insert --text=' unfold get. ' -G
  Open goals at the insertion failure (prior to document rollback):
  
  Goal 1:
    k : nat
    l : list nat
    ============================
    get k l = None
  
  The document is unchanged.
  
  Error: could not parse or process remaining text "unfold get. ".
  Anomaly "Uncaught exception Failure("nth")."
  Please report at http://rocq-prover.org/bugs/.
  [1]
  $ rocq-ed status
     3|   fun k xs => match xs with
     4|   | nil => None
     5|   | cons x xs => match k with O => Some x | S k => get k xs end
     6|   end.
     7| Lemma t (k : nat) (l : list nat) : get k l = None.
     8| Proof.<CURSOR>
     9| Admitted.
  $ rocq-ed stop

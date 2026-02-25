(* Some comment *)
Definition foo : nat := 0.
Definition bar : nat := 1.

Lemma obvious : foo <> bar. Proof. Admitted.

Definition baz : nat := -1.

Lemma obvious_again : foo <> bar. Proof. Admitted.

Lemma contra : False.
Proof. Admitted.

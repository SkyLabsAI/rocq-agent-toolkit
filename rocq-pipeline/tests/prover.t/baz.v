(* Some comment *)
Definition foo : nat = 0.
Definition bar : nat = 1.
Definition baz : nat = -1.

Lemma obvious : foo <> bar. Proof. Admitted.

Lemma contra : False.
Proof. destruct baz. Qed.

Lemma obvious_again : foo <> bar. Proof. Admitted.

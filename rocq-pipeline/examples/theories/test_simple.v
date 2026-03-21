Lemma is_true : True.
Proof. trivial. Qed.

Lemma not_false : True -> True /\ ~False.
Proof. intro. split. trivial. intro. exfalso. assumption. Qed.

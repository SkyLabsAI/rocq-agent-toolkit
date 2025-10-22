Inductive my_nat : Set :=
| MyO
| MyS (_ : my_nat).

Fixpoint my_add (a b : my_nat) : my_nat :=
  match a with
  | MyO => b
  | MyS a => my_add a (MyS b)
  end.

Lemma zero_add : forall a, my_add MyO a = a.
Proof. reflexivity. Qed.

Lemma add_S : forall a b, my_add a (MyS b) = MyS (my_add a b).
Proof. induction a; simpl; auto. Qed.

Lemma add_zero : forall a, my_add a MyO = a.
Proof. induction a; simpl; auto. rewrite add_S; congruence. Qed.

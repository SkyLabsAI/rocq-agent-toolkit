Require Import skylabs.pipeline.test.my_nat.

Lemma add_comm : forall a b, my_add a b = my_add b a.
Proof.
  induction a; simpl; intros.
  { rewrite add_zero; auto. }
  { rewrite IHa; simpl. reflexivity. }
Admitted.

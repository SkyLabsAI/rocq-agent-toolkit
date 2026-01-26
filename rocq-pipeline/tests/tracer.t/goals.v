Inductive three :=
| One
| Two
| Three.

Lemma task1 : forall x : three, x = One \/ x = Two \/ x = Three.
Proof.
  intros x.
  destruct x.
  left; reflexivity.
  right; left; reflexivity.
  right; right; reflexivity.
Qed.



About nat.

Module Foo.
  Definition foo := nat.
End Foo.

Module Bar.
  Definition bar := nat.

  Lemma refl {A : Type} (x : A) : x = x.
  Proof.
    intros. reflexivity.
  Qed. (* END *)
End Bar.

Definition other := nat.

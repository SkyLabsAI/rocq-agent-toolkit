(* Prelude. *)

Section Outer.
  Variable n : nat.

  Lemma first : True.
  Proof.
    exact I.
  Qed.

  Theorem second : n = n.
  Proof.
    reflexivity.
  Qed.

  Section Inner.
    Remark inside : True.
    Proof. exact I. Qed.
  End Inner.

  Corollary later : True.
  Proof.
    exact I.
  Qed.
End Outer.

Fact after_section : True.
Proof.
  exact I.
Qed.

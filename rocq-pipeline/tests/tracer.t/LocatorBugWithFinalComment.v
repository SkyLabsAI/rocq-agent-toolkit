Lemma locatorL1 : True.
exact I. Qed.

Lemma locatorL2 (P:Prop): P -> P.
Proof
   (fun (H : P) => H).

Check locatorL1.
(* Check locatorL2. *)
Check locatorL1.

Lemma locatorL3 : 5 <= 5.
trivial. Qed.

Lemma locatorL4 : (5=5).
Proof (eq_refl _).

(*a commend at end of file*)

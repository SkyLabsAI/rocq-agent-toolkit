Require Import skylabs.prover.test.bar.

Lemma True_is_True : True.
Proof.
Admitted.

Lemma True_and_True : True /\ True.
Proof.
Admitted.

(*
Lemma True_and_False : True /\ False.
Proof.
  split.
  - admit.
Admitted.
*)

Lemma forty_two_is_42 : forty_two = 42.
Proof.
Admitted.

Lemma forty_two_is_42_backwards : 42 = forty_two.
Proof.
Admitted.

Lemma forty_two_is_57 : forty_two = 57.
Proof.
Admitted.

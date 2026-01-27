Require Import skylabs.prover.test.bar.

Lemma True_is_True : True.
Admitted.

Lemma True_and_True : True /\ True.
Admitted.

(*
Lemma True_and_False : True /\ False.
Proof.
  split.
  - admit.
Admitted.
*)

Lemma forty_two_is_42 : forty_two = 42.
Admitted.

Lemma forty_two_is_42_backwards : 42 = forty_two.
Admitted.

Lemma forty_two_is_57 : forty_two = 57.
Admitted.

Set up environment to use dune build outputs:

  $ export DUNE_SOURCEROOT="$TESTDIR/../../../../.."
  $ [ -d "$DUNE_SOURCEROOT/_build" ] || echo "Failed to find Dune path"
  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export OCAMLPATH="$DUNE_SOURCEROOT/_build/install/default/lib"
  $ export DUNE_CACHE=disabled

Copy dune project from source tree to separate folder:

  $ cp $TESTDIR/dune-project $TESTDIR/dune $TESTDIR/*.v .


  $ cat test_with_qed.v
  Require Import skylabs.prover.test.bar.
  
  Lemma True_is_True : True.
  Proof. trivial. Qed.
  
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
  Proof. reflexivity. Defined.
  
  Lemma forty_two_is_57 : forty_two = 57.
  Proof.
  Admitted.

Run `auto-prover` via `uv`;

  $ uv run auto-prover test_with_qed.v
  Running the proving agent.
  
  Found admit at index 14.
  Goal 0:
    ============================
    True /\ True
  Agent succeeded.
  
  Found admit at index 26.
  Goal 0:
    ============================
    forty_two = 42
  Agent succeeded.
  
  Found admit at index 46.
  Goal 0:
    ============================
    forty_two = 57
  Agent failed.

  $ cat test_with_qed.v
  Require Import skylabs.prover.test.bar.
  
  Lemma True_is_True : True.
  Proof. trivial. Qed.
  
  Lemma True_and_True : True /\ True.
  Proof.
  #[local] Unset SsrIdents.
  #[local] Set Default Goal Selector "1".
  auto.
  Qed.
  
  (*
  Lemma True_and_False : True /\ False.
  Proof.
    split.
    - admit.
  Admitted.
  *)
  
  Lemma forty_two_is_42 : forty_two = 42.
  Proof.
  #[local] Unset SsrIdents.
  #[local] Set Default Goal Selector "1".
  auto.
  Qed.
  
  Lemma forty_two_is_42_backwards : 42 = forty_two.
  Proof. reflexivity. Defined.
  
  Lemma forty_two_is_57 : forty_two = 57.
  Proof.
  Admitted.


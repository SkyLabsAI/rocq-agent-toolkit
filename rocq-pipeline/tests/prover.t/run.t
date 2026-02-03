  $ export DUNE_SOURCEROOT="$TESTDIR/../../../../.."
  $ [ -d "$DUNE_SOURCEROOT/_build" ] || echo "Failed to find Dune path"
  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export OCAMLPATH="$DUNE_SOURCEROOT/_build/install/default/lib"
  $ export DUNE_CACHE=disabled

  $ cp $TESTDIR/dune-project $TESTDIR/dune $TESTDIR/*.v .

  $ uv run auto-prover foo.v
  Running the proving agent.
  
  Found admitted at index 4.
  Goal 0:
    ============================
    True
  Agent succeeded.
  
  Found admitted at index 14.
  Goal 0:
    ============================
    True /\ True
  Agent succeeded.
  
  Found admitted at index 24.
  Goal 0:
    ============================
    forty_two = 42
  Agent succeeded.
  
  Found admitted at index 34.
  Goal 0:
    ============================
    42 = forty_two
  Agent succeeded.
  
  Found admitted at index 44.
  Goal 0:
    ============================
    forty_two = 57
  Agent failed.

  $ cat foo.v
  Require Import skylabs.prover.test.bar.
  
  Lemma True_is_True : True.
  #[local] Unset SsrIdents.
  #[local] Set Default Goal Selector "1".
  auto.
  Qed.
  
  Lemma True_and_True : True /\ True.
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
  #[local] Unset SsrIdents.
  #[local] Set Default Goal Selector "1".
  auto.
  Qed.
  
  Lemma forty_two_is_42_backwards : 42 = forty_two.
  #[local] Unset SsrIdents.
  #[local] Set Default Goal Selector "1".
  auto.
  Qed.
  
  Lemma forty_two_is_57 : forty_two = 57.
  Admitted. (no-eol)

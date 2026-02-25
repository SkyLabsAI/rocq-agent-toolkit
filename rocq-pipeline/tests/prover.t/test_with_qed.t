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

Build with dune
  $ dune build --display=quiet test_with_qed.vo

Run `auto-prover` via `uv`;

  $ uv run auto-prover test_with_qed.v
  Gathering Rocq configuration...
  Loading file...
  Running the proving agent on 3 admitted proofs; partial proofs will be retained.
  
  Found admit at index 14.
  Goal 0:
    ============================
    True /\ True
  Agent succeeded.
  
  Found admit at index 22.
  Goal 0:
    ============================
    forty_two = 42
  Agent succeeded.
  
  Found admit at index 38.
  Goal 0:
    ============================
    forty_two = 57
  Agent made partial progress:
  AutoAgent: out of fuel after 1 tactic applications

  $ cat test_with_qed.v
  Require Import skylabs.prover.test.bar.
  
  Lemma True_is_True : True.
  Proof. trivial. Qed.
  
  Lemma True_and_True : True /\ True.
  Proof.
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
  auto.
  Qed.
  
  Lemma forty_two_is_42_backwards : 42 = forty_two.
  Proof. reflexivity. Defined.
  
  Lemma forty_two_is_57 : forty_two = 57.
  Proof.
  auto.
  Admitted.

Build with dune
  $ dune build --display=quiet test_with_qed.vo

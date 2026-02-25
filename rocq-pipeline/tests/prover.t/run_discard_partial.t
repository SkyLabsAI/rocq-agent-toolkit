Basic test for `auto-prover`.
Here, unlike `run-release.t.disabled`, we assume that both Python and Rocq
dependencies are only available in the workspace.
The tests are otherwise the same.

Set up environment to use dune build outputs:

  $ export DUNE_SOURCEROOT="$TESTDIR/../../../../.."
  $ [ -d "$DUNE_SOURCEROOT/_build" ] || echo "Failed to find Dune path"
  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export OCAMLPATH="$DUNE_SOURCEROOT/_build/install/default/lib"
  $ export DUNE_CACHE=disabled

Copy dune project from source tree to separate folder:

  $ cp $TESTDIR/dune-project $TESTDIR/dune $TESTDIR/*.v .

Run `auto-prover` via `uv` while discarding partial progress;

  $ uv run auto-prover foo.v --no-partial
  Gathering Rocq configuration...
  Loading file...
  Running the proving agent on 5 admitted proofs; partial proofs will be discarded.
  
  Found admit at line 5, column 0 (offset=75).
  Goal 0:
    ============================
    True
  Agent succeeded.
  
  Found admit at line 10, column 0 (offset=130).
  Goal 0:
    ============================
    True /\ True
  Agent succeeded.
  
  Found admit at line 23, column 0 (offset=271).
  Goal 0:
    ============================
    forty_two = 42
  Agent succeeded.
  
  Found admit at line 28, column 0 (offset=340).
  Goal 0:
    ============================
    42 = forty_two
  Agent succeeded.
  
  Found admit at line 33, column 0 (offset=399).
  Goal 0:
    ============================
    forty_two = 57
  Agent failed:
  AutoAgent: out of fuel after 1 tactic applications






  $ cat foo.v
  Require Import skylabs.prover.test.bar.
  
  Lemma True_is_True : True.
  Proof.
  auto.
  Qed.
  
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
  Proof.
  auto.
  Qed.
  
  Lemma forty_two_is_57 : forty_two = 57.
  Proof.
  Admitted.







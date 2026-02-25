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

Check the contents of broken/baz.v before the `auto-prover` is used.

  $ cat broken.v
  (* Some comment *)
  Definition foo : nat = 0.
  Definition bar : nat = 1.
  Definition baz : nat = -1.
  
  Lemma obvious : foo <> bar. Proof. Admitted.
  
  Lemma contra : False.
  Proof. destruct baz. Qed.
  
  Lemma obvious_again : foo <> bar. Proof. Admitted.


Run `auto-prover` via `uv` while retaining partial progress;

  $ uv run auto-prover broken.v
  Running the proving agent on 2 admitted proofs; partial proofs retained.
  
  $ cat broken.v
  (* Some comment *)
  Definition foo : nat = 0.
  Definition bar : nat = 1.
  Definition baz : nat = -1.
  
  Lemma obvious : foo <> bar. Proof. auto. Qed.
  
  Lemma contra : False.
  Proof. destruct baz. Qed.
  
  Lemma obvious_again : foo <> bar. Proof. Admitted.

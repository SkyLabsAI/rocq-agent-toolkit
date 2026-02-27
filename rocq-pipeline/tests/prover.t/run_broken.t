Basic test for `auto-prover`.
Here, unlike `run-release.t.disabled`, we assume that both Python and Rocq
dependencies are only available in the workspace.
The tests are otherwise the same.

Set up environment to use dune build outputs:

  $ export WORKSPACE="$TESTDIR/../../../../.."
  $ [ -d "$WORKSPACE/_build" ] || echo "Failed to find Dune path"
  $ export PATH="$WORKSPACE/_build/install/default/bin:$PATH"
  $ export ROCQPATH="$WORKSPACE/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$WORKSPACE/_build/install/default/lib/coq"
  $ export OCAMLPATH="$WORKSPACE/_build/install/default/lib"
  $ export DUNE_CACHE=disabled

Copy dune project from source tree to separate folder:

  $ cp $TESTDIR/dune-project $TESTDIR/dune $TESTDIR/*.v .

Check the contents of broken.v before the `auto-prover` is used.

  $ cat broken.v
  (* Some comment *)
  Definition foo : nat := 0.
  Definition bar : nat := 1.
  
  Lemma obvious : foo <> bar. Proof. Admitted.
  
  Definition baz : nat := -1.
  
  Lemma obvious_again : foo <> bar. Proof. Admitted.
  
  Lemma contra : False.
  Proof. Admitted.


Run `auto-prover` via `uv` while retaining partial progress;

  $ uv run auto-prover broken.v
  Gathering Rocq configuration...
  Loading file...
  Running the proving agent on 3 admitted proofs; partial proofs will be retained.
  
  Found admit at line 6, column 35 (offset=109).
  Goal 0:
    ============================
    foo <> bar
  Agent succeeded.
  
  Command failure after processing 1 admitted proof:
  
  Definition baz : nat := -1.
  
  Cannot interpret this number as a value of type nat

  $ cat broken.v
  (* Some comment *)
  Definition foo : nat := 0.
  Definition bar : nat := 1.
  
  Lemma obvious : foo <> bar. Proof. auto.
  Qed.
  
  Definition baz : nat := -1.
  
  Lemma obvious_again : foo <> bar. Proof. Admitted.
  
  Lemma contra : False.
  Proof. Admitted.

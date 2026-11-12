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


  $ cat test.v
  Set Default Goal Selector "!".
  Goal True.
  Proof. Admitted.
  
  Set Default Goal Selector "1".
  Goal True.
  Proof. Admitted.

Build with dune
  $ dune build --display=quiet

Run `auto-prover` via `uv`;

  $ uv run auto-prover test.v
  Gathering Rocq configuration...
  Loading file...
  Running the proving agent on 2 admitted proofs; partial proofs will be retained.
  
  Found admit at line 4, column 7 (offset=49).
  Goal 0:
    ============================
    True
  Agent succeeded.
  
  Found admit at line 10, column 7 (offset=150).
  Goal 0:
    ============================
    True
  Agent succeeded.

  $ cat test.v
  Set Default Goal Selector "!".
  Goal True.
  Proof. #[local] Set Default Goal Selector "1".
  auto.
  Qed.
  
  Set Default Goal Selector "1".
  Goal True.
  Proof. auto.
  Qed.

Build with dune
  $ dune build --display=quiet

Set up environment to use dune build outputs:

  $ export DUNE_SOURCEROOT="$TESTDIR/../../../../.."
  $ [ -d "$DUNE_SOURCEROOT/_build" ] || echo "Failed to find Dune path"
  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export OCAMLPATH="$DUNE_SOURCEROOT/_build/install/default/lib"
  $ export DUNE_CACHE=disabled

Copy dune project from source tree to separate folder:

  $ cp $TESTDIR/dune-project $TESTDIR/dune $TESTDIR/*.v .


  $ cat test.v
  Require Import ssreflect.
  
  Set Default Goal Selector "!".
  Set SsrIdents.
  Goal True.
  Proof. Admitted.
  
  Set Default Goal Selector "1".
  Set SsrIdents.
  Goal True.
  Proof. Admitted.
  
  Set Default Goal Selector "1".
  Unset SsrIdents.
  Goal True.
  Proof. Admitted.
  
  Set Default Goal Selector "!".
  Unset SsrIdents.
  Goal True.
  Proof. Admitted.

Build with dune
  $ dune build --display=quiet

Run `auto-prover` via `uv`;

  $ uv run auto-prover test.v
  Gathering Rocq configuration...
  Loading file...
  Running the proving agent on 4 admitted proofs; partial proofs will be retained.
  
  Found admit at index 10.
  Goal 0:
    ============================
    True
  Agent succeeded.
  
  Found admit at index 26.
  Goal 0:
    ============================
    True
  Agent succeeded.
  
  Found admit at index 40.
  Goal 0:
    ============================
    True
  Agent succeeded.
  
  Found admit at index 52.
  Goal 0:
    ============================
    True
  Agent succeeded.

  $ cat test.v
  Require Import ssreflect.
  
  Set Default Goal Selector "!".
  Set SsrIdents.
  Goal True.
  Proof. #[local] Unset SsrIdents.
  #[local] Set Default Goal Selector "1".
  auto.
  Qed.
  
  Set Default Goal Selector "1".
  Set SsrIdents.
  Goal True.
  Proof. #[local] Unset SsrIdents.
  auto.
  Qed.
  
  Set Default Goal Selector "1".
  Unset SsrIdents.
  Goal True.
  Proof. auto.
  Qed.
  
  Set Default Goal Selector "!".
  Unset SsrIdents.
  Goal True.
  Proof. #[local] Set Default Goal Selector "1".
  auto.
  Qed.

Build with dune
  $ dune build --display=quiet

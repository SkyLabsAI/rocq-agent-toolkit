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
  
  Found admit at line 7, column 7 (offset=91).
  Goal 0:
    ============================
    True
  Agent succeeded.
  
  Found admit at line 15, column 7 (offset=233).
  Goal 0:
    ============================
    True
  Agent succeeded.
  
  Found admit at line 22, column 7 (offset=337).
  Goal 0:
    ============================
    True
  Agent succeeded.
  
  Found admit at line 28, column 7 (offset=415).
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

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

Run `auto-prover` via `uv`;

  $ dune b foo.vo
  $ uv run auto-prover foo.v
  Running the proving agent.
  
  Found admit at index 14.
  Goal 0:
    ============================
    forall a : my_nat, my_add MyO a = a
  Agent succeeded.











  $ cat foo.v
  Require Import Stdlib.Strings.String.
  
  Open Scope string_scope.
  Inductive my_nat : Set :=
  | MyO
  | MyS (_ : my_nat).
  
  (* Trap 1: Comment containing the target text *)
  (* TODO: If the induction gets too messy, just use Proof. Admitted. *)
  
  (* Trap 2: String literal containing the target text *)
  Definition fallback_string := "Failed to solve; left as Proof. Admitted.".
  
  Fixpoint my_add (a b : my_nat) : my_nat :=
    match a with
    | MyO => b
    | MyS a => my_add a (MyS b)
    end.
  
  Lemma zero_add : forall a, my_add MyO a = a.
  Proof. #[local] Unset SsrIdents.
  #[local] Set Default Goal Selector "1".
  auto.
  Qed.














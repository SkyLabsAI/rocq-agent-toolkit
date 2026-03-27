  $ export WORKSPACE="$TESTDIR/../../../.."
  $ export PATH="$WORKSPACE/_build/install/default/bin:$PATH"
  $ export ROCQPATH="$WORKSPACE/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$WORKSPACE/_build/install/default/lib/coq"
  $ export OCAMLPATH="$WORKSPACE/_build/install/default/lib"
  $ export DUNE_CACHE=disabled

  $ mkdir deterministic_name && cd deterministic_name
  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > (name test)
  > EOF

  $ cat > dune <<EOF
  > (include_subdirs qualified)
  > (rocq.theory
  >  (name roq_agent_toolkit.cram.multi_task)
  >  (theories
  >   Stdlib Ltac2
  >   Equations Equations.Prop Equations.Type))
  > EOF
  $ cat > test.v <<EOF
  > Lemma test : True /\ True.
  > Proof.
  >   split; trivial.
  > Qed.
  > EOF

  $ uv run tacinterp -1 test.v Lemma:test
  0/ split; trivial.
    > run_command("1: split.")
    > run_command("1: trivial.")
    > run_command("1: trivial.")

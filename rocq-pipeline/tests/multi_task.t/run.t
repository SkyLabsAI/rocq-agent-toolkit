  $ export DUNE_SOURCEROOT="$TESTDIR/../../../../.."
  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export OCAMLPATH="$DUNE_SOURCEROOT/_build/install/default/lib"
  $ export DUNE_CACHE=disabled
  $ cat > dune-project <<EOF
  > (lang dune 3.17)
  > (using coq 0.10)
  > EOF
  $ cat > dune <<EOF
  > (include_subdirs qualified)
  > (coq.theory
  >  (name roq_agent_toolkit.cram.multi_task)
  >  (theories
  >   Stdlib Ltac2
  >   Equations Equations.Prop Equations.Type))
  > EOF

  $ cp $TESTDIR/* .
  $ uv run rat ingest test.v 2> /dev/null
  Found 4 tasks in test.v: ['Lemma:test', 'Lemma:test(1)', 'Theorem:test', 'Theorem:test(1)']
  Total number of tasks: 4
  Total number of unique tasks: 4

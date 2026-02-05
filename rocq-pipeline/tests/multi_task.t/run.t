  $ export DUNE_SOURCEROOT="$TESTDIR/../../../../.."
  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export OCAMLPATH="$DUNE_SOURCEROOT/_build/install/default/lib"
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
  $ cp $TESTDIR/* .

  $ git init -b main > /dev/null
  $ git config user.name "Tester"
  $ git config user.email "tester@example.com"
  $ git remote add origin git@github.com:example/example.git
  $ git add dune dune-project test.v
  $ git commit -m "Test." > /dev/null

  $ uv run rat ingest --verbose -o tasks.yaml test.v
  INFO: Number of Rocq source files found: 1
  INFO: Only keeping the files passed on the command line.
  INFO: Found 4 tasks in test.v: Lemma:test, Lemma:test(1), Theorem:test, ...
  INFO: Total number of tasks: 4
  INFO: Total number of unique tasks: 4

  $ export DUNE_SOURCEROOT="$TESTDIR/../../../.."
  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export OCAMLPATH="$DUNE_SOURCEROOT/_build/install/default/lib"
  $ export DUNE_CACHE=disabled

  $ mkdir deterministic_name && cd deterministic_name
  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF
  $ cat > dune <<EOF
  > (include_subdirs qualified)
  > (rocq.theory
  >  (name rocq_agent_toolkit.cram.simple_tools)
  >  (theories
  >   Stdlib Ltac2
  >   Equations Equations.Prop Equations.Type))
  > EOF
  $ cp -r $TESTDIR/theories .

  $ uv run tool-tester theories/test1.v Lemma:test \
  > '"current_goals"' \
  > '[["run_tactic", {"tactic": "split."}],["current_goals", {}]]' \
  > '"proof_script"' \
  > '[["run_tactic", {"tactic": "trivial."}]]' \
  > '"proof_script"' \
  > '[["backtrack", {"count": 1}]]' \
  > '"proof_script"' \
  > '"current_goals"' \
  > '[["run_tactic", {"tactic": "trivial."}]]' \
  > '[["run_tactic", {"tactic": "trivial."}]]' \
  > '"proof_script"'
  current_goals({})
  = ['\n============================\nTrue /\\ True']
  run_tactic({'tactic': 'split.'})
  current_goals({})
  = error=None result=['\n============================\nTrue', '\n============================\nTrue']
  = ['\n============================\nTrue', '\n============================\nTrue']
  proof_script({})
  = ['split.']
  run_tactic({'tactic': 'trivial.'})
  = error=None result=['\n============================\nTrue']
  proof_script({})
  = ['split.', 'trivial.']
  backtrack({'count': 1})
  = True
  proof_script({})
  = ['split.']
  current_goals({})
  = ['\n============================\nTrue', '\n============================\nTrue']
  run_tactic({'tactic': 'trivial.'})
  = error=None result=['\n============================\nTrue']
  run_tactic({'tactic': 'trivial.'})
  = error=None result=[]
  proof_script({})
  = ['split.', 'trivial.', 'trivial.']

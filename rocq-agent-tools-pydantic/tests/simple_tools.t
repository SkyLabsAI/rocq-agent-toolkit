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
  > '["insert_tactics", {"text": "(* comment *) idtac. try reflexivity.\n"}]' \
  > '"proof_script"' \
  > '["insert_tactics", {"text": "idtac. broken text"}]' \
  > '"proof_script"' \
  > '["insert_tactics", {"text": " simply broken."}]' \
  > '"proof_script"' \
  > '["run_tactic", {"tactic": "split."}]' \
  > '"proof_script"' \
  > '["run_tactic", {"tactic": "trivial."}]' \
  > '"proof_script"' \
  > '["backtrack", {"count": 1}]' \
  > '"proof_script"' \
  > '"current_goals"' \
  > '["run_tactic", {"tactic": "trivial."}]' \
  > '["run_tactic", {"tactic": "trivial."}]' \
  > '"proof_script"'
  current_goals({})
  = ['\n============================\nTrue /\\ True']
  insert_tactics({'text': '(* comment *) idtac. try reflexivity.\n'})
  = error=None result=(2, None, ['\n============================\nTrue /\\ True'])
  proof_script({})
  = ['idtac.', 'try reflexivity.']
  insert_tactics({'text': 'idtac. broken text'})
  = error='Syntax error: [ltac_use_default] expected after [tactic] (in [tactic_command]).' result=(1, ' broken text', ['\n============================\nTrue /\\ True'])
  proof_script({})
  = ['idtac.', 'try reflexivity.', 'idtac.']
  insert_tactics({'text': ' simply broken.'})
  = error='The reference simply was not found in the current environment.' result=(0, 'simply broken.', None)
  proof_script({})
  = ['idtac.', 'try reflexivity.', 'idtac.']
  run_tactic({'tactic': 'split.'})
  = error=None result=['\n============================\nTrue', '\n============================\nTrue']
  proof_script({})
  = ['idtac.', 'try reflexivity.', 'idtac.', 'split.']
  run_tactic({'tactic': 'trivial.'})
  = error=None result=['\n============================\nTrue']
  proof_script({})
  = ['idtac.', 'try reflexivity.', 'idtac.', 'split.', 'trivial.']
  backtrack({'count': 1})
  = True
  proof_script({})
  = ['idtac.', 'try reflexivity.', 'idtac.', 'split.']
  current_goals({})
  = ['\n============================\nTrue', '\n============================\nTrue']
  run_tactic({'tactic': 'trivial.'})
  = error=None result=['\n============================\nTrue']
  run_tactic({'tactic': 'trivial.'})
  = error=None result=[]
  proof_script({})
  = ['idtac.', 'try reflexivity.', 'idtac.', 'split.', 'trivial.', 'trivial.']

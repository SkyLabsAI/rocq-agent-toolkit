  $ export WORKSPACE="$TESTDIR/../../../../.."
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
  $ cp $TESTDIR/test.v .

  $ cat > tasks_with_mod.yaml <<EOF
  > project_bundles:
  > - project:
  >     name: dummy
  >     git_url: dummy
  >     git_commit: dummy
  >     path: .
  >   tasks:
  >   - file: test.v
  >     locator: Lemma:lem1
  >     modifiers:
  >     - {"insert_command": {"commands": ["Opaque foo."], "ghost": true}}
  > EOF
  $ cat > tasks_without_mod.yaml <<EOF
  > project_bundles:
  > - project:
  >     name: dummy
  >     git_url: dummy
  >     git_commit: dummy
  >     path: .
  >   tasks:
  >   - file: test.v
  >     locator: Lemma:lem1
  > EOF

  $ rat run --agent $TESTDIR/puppet.py:puppet_builder --task-file tasks_without_mod.yaml -- 'About foo.'
  proof_state=ProofState(focused_goals=['\n============================\nTrue'], unfocused_goals=[], shelved_goals=0, given_up_goals=0) feedback_messages=[FeedbackMessage(text='foo : nat\n\nfoo is not universe polymorphic\nfoo is transparent\nExpands to: Constant test.foo\nDeclared in toplevel input, characters 11-14', quickfix=[], loc=None, level='notice')] globrefs_diff=GlobrefsDiff(removed_inductives=[], added_inductives=[], removed_constants=[], added_constants=[])
  dummy#dummy#test.v#Lemma:lem1: PuppetAgent gave up with message: completed 
  interactions
  
  Finished 1 tasks: 0 Success, 1 Failures



  $ rat run --agent $TESTDIR/puppet.py:puppet_builder --task-file tasks_with_mod.yaml -- 'About foo.'
  proof_state=ProofState(focused_goals=['\n============================\nTrue'], unfocused_goals=[], shelved_goals=0, given_up_goals=0) feedback_messages=[FeedbackMessage(text='foo : nat\n\nfoo is not universe polymorphic\nfoo is opaque but may be made transparent\nExpands to: Constant test.foo\nDeclared in toplevel input, characters 11-14', quickfix=[], loc=None, level='notice')] globrefs_diff=GlobrefsDiff(removed_inductives=[], added_inductives=[], removed_constants=[], added_constants=[])
  dummy#dummy#test.v#Lemma:lem1: PuppetAgent gave up with message: completed 
  interactions
  
  Finished 1 tasks: 0 Success, 1 Failures



  $ rat run --agent $TESTDIR/puppet.py:puppet_builder --task-file tasks_without_mod.yaml \
  >    --task-mod '{"insert_command": {"commands": ["Opaque foo."], "ghost": true}}' -- 'About foo.'
  proof_state=ProofState(focused_goals=['\n============================\nTrue'], unfocused_goals=[], shelved_goals=0, given_up_goals=0) feedback_messages=[FeedbackMessage(text='foo : nat\n\nfoo is not universe polymorphic\nfoo is opaque but may be made transparent\nExpands to: Constant test.foo\nDeclared in toplevel input, characters 11-14', quickfix=[], loc=None, level='notice')] globrefs_diff=GlobrefsDiff(removed_inductives=[], added_inductives=[], removed_constants=[], added_constants=[])
  dummy#dummy#test.v#Lemma:lem1: PuppetAgent gave up with message: completed 
  interactions
  
  Finished 1 tasks: 0 Success, 1 Failures


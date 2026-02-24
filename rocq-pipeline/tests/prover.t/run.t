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

  $ uv run auto-prover foo.v
  Running auto_prover()
  Running agent with Rocq arguments: ['-w', '-deprecated-native-compiler-option', '-w', '-native-compiler-disabled', '-native-compiler', 'ondemand', '-boot', '-R', '/Users/pgiarrusso1/git-sl/workspace/fmdeps/rocq-agent-toolkit/rocq-pipeline/tests/prover.t/../../../../../_build/install/default/lib/coq/theories', 'Corelib', '-Q', '/Users/pgiarrusso1/git-sl/workspace/fmdeps/rocq-agent-toolkit/rocq-pipeline/tests/prover.t/../../../../../_build/install/default/lib/coq/user-contrib/Stdlib', 'Stdlib', '-Q', '/Users/pgiarrusso1/git-sl/workspace/fmdeps/rocq-agent-toolkit/rocq-pipeline/tests/prover.t/../../../../../_build/install/default/lib/coq/user-contrib/Ltac2', 'Ltac2', '-R', '/private/var/folders/6q/2ycxnczj1qsgwsk7lg3yd4bh0000gn/T/cramtests-t5_vd809/run.t/_build/default', 'skylabs.prover.test'], agent args: [], on file: foo.v; agent_builder config: <rocq_pipeline.agent.base.classes.AgentBuilder object at 0x109ad0ec0>
  Running the proving agent.
  Doc: [], [SuffixItem(text='Require Import skylabs.prover.test.bar.', kind='command'), SuffixItem(text='\n\n', kind='blanks'), SuffixItem(text='Lemma True_is_True : True.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Proof.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Admitted.', kind='command'), SuffixItem(text='\n\n', kind='blanks'), SuffixItem(text='Lemma True_and_True : True /\\ True.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Proof.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Admitted.', kind='command'), SuffixItem(text='\n\n(*\nLemma True_and_False : True /\\ False.\nProof.\n  split.\n  - admit.\nAdmitted.\n*)\n\n', kind='blanks'), SuffixItem(text='Lemma forty_two_is_42 : forty_two = 42.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Proof.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Admitted.', kind='command'), SuffixItem(text='\n\n', kind='blanks'), SuffixItem(text='Lemma forty_two_is_42_backwards : 42 = forty_two.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Proof.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Admitted.', kind='command'), SuffixItem(text='\n\n', kind='blanks'), SuffixItem(text='Lemma forty_two_is_57 : forty_two = 57.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Proof.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Admitted.', kind='command'), SuffixItem(text='\n', kind='blanks')]
  
  Doc: [PrefixItem(text='Require Import skylabs.prover.test.bar.', offset=0, kind='command'), PrefixItem(text='\n\n', offset=39, kind='blanks'), PrefixItem(text='Lemma True_is_True : True.', offset=41, kind='command'), PrefixItem(text='\n', offset=67, kind='blanks'), PrefixItem(text='Proof.', offset=68, kind='command'), PrefixItem(text='\n', offset=74, kind='blanks')], [SuffixItem(text='Admitted.', kind='command'), SuffixItem(text='\n\n', kind='blanks'), SuffixItem(text='Lemma True_and_True : True /\\ True.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Proof.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Admitted.', kind='command'), SuffixItem(text='\n\n(*\nLemma True_and_False : True /\\ False.\nProof.\n  split.\n  - admit.\nAdmitted.\n*)\n\n', kind='blanks'), SuffixItem(text='Lemma forty_two_is_42 : forty_two = 42.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Proof.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Admitted.', kind='command'), SuffixItem(text='\n\n', kind='blanks'), SuffixItem(text='Lemma forty_two_is_42_backwards : 42 = forty_two.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Proof.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Admitted.', kind='command'), SuffixItem(text='\n\n', kind='blanks'), SuffixItem(text='Lemma forty_two_is_57 : forty_two = 57.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Proof.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Admitted.', kind='command'), SuffixItem(text='\n', kind='blanks')]
  Found admit at index 6.
  Goal 0:
    ============================
    True
  Agent succeeded.
  
  Doc: [PrefixItem(text='Require Import skylabs.prover.test.bar.', offset=0, kind='command'), PrefixItem(text='\n\n', offset=39, kind='blanks'), PrefixItem(text='Lemma True_is_True : True.', offset=41, kind='command'), PrefixItem(text='\n', offset=67, kind='blanks'), PrefixItem(text='Proof.', offset=68, kind='command'), PrefixItem(text='\n', offset=74, kind='blanks'), PrefixItem(text='#[local] Unset SsrIdents.', offset=75, kind='command'), PrefixItem(text='\n', offset=100, kind='blanks'), PrefixItem(text='#[local] Set Default Goal Selector "1".', offset=101, kind='command'), PrefixItem(text='\n', offset=140, kind='blanks'), PrefixItem(text='auto.', offset=141, kind='command'), PrefixItem(text='\n', offset=146, kind='blanks'), PrefixItem(text='Qed.', offset=147, kind='command'), PrefixItem(text='\n\n', offset=151, kind='blanks'), PrefixItem(text='Lemma True_and_True : True /\\ True.', offset=153, kind='command'), PrefixItem(text='\n', offset=188, kind='blanks'), PrefixItem(text='Proof.', offset=189, kind='command'), PrefixItem(text='\n', offset=195, kind='blanks')], [SuffixItem(text='Admitted.', kind='command'), SuffixItem(text='\n\n(*\nLemma True_and_False : True /\\ False.\nProof.\n  split.\n  - admit.\nAdmitted.\n*)\n\n', kind='blanks'), SuffixItem(text='Lemma forty_two_is_42 : forty_two = 42.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Proof.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Admitted.', kind='command'), SuffixItem(text='\n\n', kind='blanks'), SuffixItem(text='Lemma forty_two_is_42_backwards : 42 = forty_two.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Proof.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Admitted.', kind='command'), SuffixItem(text='\n\n', kind='blanks'), SuffixItem(text='Lemma forty_two_is_57 : forty_two = 57.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Proof.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Admitted.', kind='command'), SuffixItem(text='\n', kind='blanks')]
  Found admit at index 18.
  Goal 0:
    ============================
    True /\ True
  Agent succeeded.
  
  Doc: [PrefixItem(text='Require Import skylabs.prover.test.bar.', offset=0, kind='command'), PrefixItem(text='\n\n', offset=39, kind='blanks'), PrefixItem(text='Lemma True_is_True : True.', offset=41, kind='command'), PrefixItem(text='\n', offset=67, kind='blanks'), PrefixItem(text='Proof.', offset=68, kind='command'), PrefixItem(text='\n', offset=74, kind='blanks'), PrefixItem(text='#[local] Unset SsrIdents.', offset=75, kind='command'), PrefixItem(text='\n', offset=100, kind='blanks'), PrefixItem(text='#[local] Set Default Goal Selector "1".', offset=101, kind='command'), PrefixItem(text='\n', offset=140, kind='blanks'), PrefixItem(text='auto.', offset=141, kind='command'), PrefixItem(text='\n', offset=146, kind='blanks'), PrefixItem(text='Qed.', offset=147, kind='command'), PrefixItem(text='\n\n', offset=151, kind='blanks'), PrefixItem(text='Lemma True_and_True : True /\\ True.', offset=153, kind='command'), PrefixItem(text='\n', offset=188, kind='blanks'), PrefixItem(text='Proof.', offset=189, kind='command'), PrefixItem(text='\n', offset=195, kind='blanks'), PrefixItem(text='#[local] Unset SsrIdents.', offset=196, kind='command'), PrefixItem(text='\n', offset=221, kind='blanks'), PrefixItem(text='#[local] Set Default Goal Selector "1".', offset=222, kind='command'), PrefixItem(text='\n', offset=261, kind='blanks'), PrefixItem(text='auto.', offset=262, kind='command'), PrefixItem(text='\n', offset=267, kind='blanks'), PrefixItem(text='Qed.', offset=268, kind='command'), PrefixItem(text='\n\n(*\nLemma True_and_False : True /\\ False.\nProof.\n  split.\n  - admit.\nAdmitted.\n*)\n\n', offset=272, kind='blanks'), PrefixItem(text='Lemma forty_two_is_42 : forty_two = 42.', offset=356, kind='command'), PrefixItem(text='\n', offset=395, kind='blanks'), PrefixItem(text='Proof.', offset=396, kind='command'), PrefixItem(text='\n', offset=402, kind='blanks')], [SuffixItem(text='Admitted.', kind='command'), SuffixItem(text='\n\n', kind='blanks'), SuffixItem(text='Lemma forty_two_is_42_backwards : 42 = forty_two.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Proof.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Admitted.', kind='command'), SuffixItem(text='\n\n', kind='blanks'), SuffixItem(text='Lemma forty_two_is_57 : forty_two = 57.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Proof.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Admitted.', kind='command'), SuffixItem(text='\n', kind='blanks')]
  Found admit at index 30.
  Goal 0:
    ============================
    forty_two = 42
  Agent succeeded.
  
  Doc: [PrefixItem(text='Require Import skylabs.prover.test.bar.', offset=0, kind='command'), PrefixItem(text='\n\n', offset=39, kind='blanks'), PrefixItem(text='Lemma True_is_True : True.', offset=41, kind='command'), PrefixItem(text='\n', offset=67, kind='blanks'), PrefixItem(text='Proof.', offset=68, kind='command'), PrefixItem(text='\n', offset=74, kind='blanks'), PrefixItem(text='#[local] Unset SsrIdents.', offset=75, kind='command'), PrefixItem(text='\n', offset=100, kind='blanks'), PrefixItem(text='#[local] Set Default Goal Selector "1".', offset=101, kind='command'), PrefixItem(text='\n', offset=140, kind='blanks'), PrefixItem(text='auto.', offset=141, kind='command'), PrefixItem(text='\n', offset=146, kind='blanks'), PrefixItem(text='Qed.', offset=147, kind='command'), PrefixItem(text='\n\n', offset=151, kind='blanks'), PrefixItem(text='Lemma True_and_True : True /\\ True.', offset=153, kind='command'), PrefixItem(text='\n', offset=188, kind='blanks'), PrefixItem(text='Proof.', offset=189, kind='command'), PrefixItem(text='\n', offset=195, kind='blanks'), PrefixItem(text='#[local] Unset SsrIdents.', offset=196, kind='command'), PrefixItem(text='\n', offset=221, kind='blanks'), PrefixItem(text='#[local] Set Default Goal Selector "1".', offset=222, kind='command'), PrefixItem(text='\n', offset=261, kind='blanks'), PrefixItem(text='auto.', offset=262, kind='command'), PrefixItem(text='\n', offset=267, kind='blanks'), PrefixItem(text='Qed.', offset=268, kind='command'), PrefixItem(text='\n\n(*\nLemma True_and_False : True /\\ False.\nProof.\n  split.\n  - admit.\nAdmitted.\n*)\n\n', offset=272, kind='blanks'), PrefixItem(text='Lemma forty_two_is_42 : forty_two = 42.', offset=356, kind='command'), PrefixItem(text='\n', offset=395, kind='blanks'), PrefixItem(text='Proof.', offset=396, kind='command'), PrefixItem(text='\n', offset=402, kind='blanks'), PrefixItem(text='#[local] Unset SsrIdents.', offset=403, kind='command'), PrefixItem(text='\n', offset=428, kind='blanks'), PrefixItem(text='#[local] Set Default Goal Selector "1".', offset=429, kind='command'), PrefixItem(text='\n', offset=468, kind='blanks'), PrefixItem(text='auto.', offset=469, kind='command'), PrefixItem(text='\n', offset=474, kind='blanks'), PrefixItem(text='Qed.', offset=475, kind='command'), PrefixItem(text='\n\n', offset=479, kind='blanks'), PrefixItem(text='Lemma forty_two_is_42_backwards : 42 = forty_two.', offset=481, kind='command'), PrefixItem(text='\n', offset=530, kind='blanks'), PrefixItem(text='Proof.', offset=531, kind='command'), PrefixItem(text='\n', offset=537, kind='blanks')], [SuffixItem(text='Admitted.', kind='command'), SuffixItem(text='\n\n', kind='blanks'), SuffixItem(text='Lemma forty_two_is_57 : forty_two = 57.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Proof.', kind='command'), SuffixItem(text='\n', kind='blanks'), SuffixItem(text='Admitted.', kind='command'), SuffixItem(text='\n', kind='blanks')]
  Found admit at index 42.
  Goal 0:
    ============================
    42 = forty_two
  Agent succeeded.
  
  Doc: [PrefixItem(text='Require Import skylabs.prover.test.bar.', offset=0, kind='command'), PrefixItem(text='\n\n', offset=39, kind='blanks'), PrefixItem(text='Lemma True_is_True : True.', offset=41, kind='command'), PrefixItem(text='\n', offset=67, kind='blanks'), PrefixItem(text='Proof.', offset=68, kind='command'), PrefixItem(text='\n', offset=74, kind='blanks'), PrefixItem(text='#[local] Unset SsrIdents.', offset=75, kind='command'), PrefixItem(text='\n', offset=100, kind='blanks'), PrefixItem(text='#[local] Set Default Goal Selector "1".', offset=101, kind='command'), PrefixItem(text='\n', offset=140, kind='blanks'), PrefixItem(text='auto.', offset=141, kind='command'), PrefixItem(text='\n', offset=146, kind='blanks'), PrefixItem(text='Qed.', offset=147, kind='command'), PrefixItem(text='\n\n', offset=151, kind='blanks'), PrefixItem(text='Lemma True_and_True : True /\\ True.', offset=153, kind='command'), PrefixItem(text='\n', offset=188, kind='blanks'), PrefixItem(text='Proof.', offset=189, kind='command'), PrefixItem(text='\n', offset=195, kind='blanks'), PrefixItem(text='#[local] Unset SsrIdents.', offset=196, kind='command'), PrefixItem(text='\n', offset=221, kind='blanks'), PrefixItem(text='#[local] Set Default Goal Selector "1".', offset=222, kind='command'), PrefixItem(text='\n', offset=261, kind='blanks'), PrefixItem(text='auto.', offset=262, kind='command'), PrefixItem(text='\n', offset=267, kind='blanks'), PrefixItem(text='Qed.', offset=268, kind='command'), PrefixItem(text='\n\n(*\nLemma True_and_False : True /\\ False.\nProof.\n  split.\n  - admit.\nAdmitted.\n*)\n\n', offset=272, kind='blanks'), PrefixItem(text='Lemma forty_two_is_42 : forty_two = 42.', offset=356, kind='command'), PrefixItem(text='\n', offset=395, kind='blanks'), PrefixItem(text='Proof.', offset=396, kind='command'), PrefixItem(text='\n', offset=402, kind='blanks'), PrefixItem(text='#[local] Unset SsrIdents.', offset=403, kind='command'), PrefixItem(text='\n', offset=428, kind='blanks'), PrefixItem(text='#[local] Set Default Goal Selector "1".', offset=429, kind='command'), PrefixItem(text='\n', offset=468, kind='blanks'), PrefixItem(text='auto.', offset=469, kind='command'), PrefixItem(text='\n', offset=474, kind='blanks'), PrefixItem(text='Qed.', offset=475, kind='command'), PrefixItem(text='\n\n', offset=479, kind='blanks'), PrefixItem(text='Lemma forty_two_is_42_backwards : 42 = forty_two.', offset=481, kind='command'), PrefixItem(text='\n', offset=530, kind='blanks'), PrefixItem(text='Proof.', offset=531, kind='command'), PrefixItem(text='\n', offset=537, kind='blanks'), PrefixItem(text='#[local] Unset SsrIdents.', offset=538, kind='command'), PrefixItem(text='\n', offset=563, kind='blanks'), PrefixItem(text='#[local] Set Default Goal Selector "1".', offset=564, kind='command'), PrefixItem(text='\n', offset=603, kind='blanks'), PrefixItem(text='auto.', offset=604, kind='command'), PrefixItem(text='\n', offset=609, kind='blanks'), PrefixItem(text='Qed.', offset=610, kind='command'), PrefixItem(text='\n\n', offset=614, kind='blanks'), PrefixItem(text='Lemma forty_two_is_57 : forty_two = 57.', offset=616, kind='command'), PrefixItem(text='\n', offset=655, kind='blanks'), PrefixItem(text='Proof.', offset=656, kind='command'), PrefixItem(text='\n', offset=662, kind='blanks')], [SuffixItem(text='Admitted.', kind='command'), SuffixItem(text='\n', kind='blanks')]
  Found admit at index 54.
  Goal 0:
    ============================
    forty_two = 57
  Agent failed.






  $ cat foo.v
  Require Import skylabs.prover.test.bar.
  
  Lemma True_is_True : True.
  Proof.
  #[local] Unset SsrIdents.
  #[local] Set Default Goal Selector "1".
  auto.
  Qed.
  
  Lemma True_and_True : True /\ True.
  Proof.
  #[local] Unset SsrIdents.
  #[local] Set Default Goal Selector "1".
  auto.
  Qed.
  
  (*
  Lemma True_and_False : True /\ False.
  Proof.
    split.
    - admit.
  Admitted.
  *)
  
  Lemma forty_two_is_42 : forty_two = 42.
  Proof.
  #[local] Unset SsrIdents.
  #[local] Set Default Goal Selector "1".
  auto.
  Qed.
  
  Lemma forty_two_is_42_backwards : 42 = forty_two.
  Proof.
  #[local] Unset SsrIdents.
  #[local] Set Default Goal Selector "1".
  auto.
  Qed.
  
  Lemma forty_two_is_57 : forty_two = 57.
  Proof.
  Admitted.







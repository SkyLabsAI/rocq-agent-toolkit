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
  >  (name roq_agent_toolkit.cram.tracer)
  >  (theories
  >   Stdlib Ltac2))
  > EOF
  $ cp $TESTDIR/* .


  $ uv run rat ingest --output tasks.yaml *.v
  WARNING: The project does not seem to use git for versioning.
  $ uv run rat trace --tracer rocq_pipeline.tracers.string_goal --task-file tasks.yaml
  



  $ LC_ALL=C ls *.json | sort
  LocatorBug.v_Lemma:locatorL1.json
  LocatorBug.v_Lemma:locatorL2.json
  LocatorBug.v_Lemma:locatorL3.json
  LocatorBug.v_Lemma:locatorL4.json
  LocatorBugWithFinalComment.v_Lemma:locatorL1.json
  LocatorBugWithFinalComment.v_Lemma:locatorL2.json
  LocatorBugWithFinalComment.v_Lemma:locatorL3.json
  LocatorBugWithFinalComment.v_Lemma:locatorL4.json
  TracerBug.v_Lemma:L1.json
  TracerBug.v_Lemma:L2.json
  goals.v_Lemma:task1.json

  $ LC_ALL=C ls *.json | sort | xargs -n 1 python3 -m json.tool
  [
      {
          "before": "1 Goal Total\n\t1 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n\n============================\nTrue",
          "after": "0 Goal Total\n\t0 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n",
          "tactic": "exact I"
      }
  ]
  [
      {
          "before": "1 Goal Total\n\t1 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n\nP : Prop\n============================\nP -> P",
          "after": "0 Goal Total\n\t0 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n",
          "tactic": "Proof\n   (fun (H : P) => H)"
      }
  ]
  [
      {
          "before": "1 Goal Total\n\t1 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n\n============================\n5 <= 5",
          "after": "0 Goal Total\n\t0 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n",
          "tactic": "trivial"
      }
  ]
  [
      {
          "before": "1 Goal Total\n\t1 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n\n============================\n5 = 5",
          "after": "0 Goal Total\n\t0 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n",
          "tactic": "Proof (eq_refl _)"
      }
  ]
  [
      {
          "before": "1 Goal Total\n\t1 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n\n============================\nTrue",
          "after": "0 Goal Total\n\t0 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n",
          "tactic": "exact I"
      }
  ]
  [
      {
          "before": "1 Goal Total\n\t1 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n\nP : Prop\n============================\nP -> P",
          "after": "0 Goal Total\n\t0 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n",
          "tactic": "Proof\n   (fun (H : P) => H)"
      }
  ]
  [
      {
          "before": "1 Goal Total\n\t1 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n\n============================\n5 <= 5",
          "after": "0 Goal Total\n\t0 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n",
          "tactic": "trivial"
      }
  ]
  [
      {
          "before": "1 Goal Total\n\t1 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n\n============================\n5 = 5",
          "after": "0 Goal Total\n\t0 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n",
          "tactic": "Proof (eq_refl _)"
      }
  ]
  [
      {
          "before": "1 Goal Total\n\t1 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n\n============================\nTrue",
          "after": "0 Goal Total\n\t0 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n",
          "tactic": "Proof I"
      }
  ]
  [
      {
          "before": "1 Goal Total\n\t1 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n\n============================\n5 = 5",
          "after": "0 Goal Total\n\t0 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n",
          "tactic": "Proof (eq_refl _)"
      }
  ]
  [
      {
          "before": "1 Goal Total\n\t1 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n\n============================\nforall x : three, x = One \\/ x = Two \\/ x = Three",
          "after": "1 Goal Total\n\t1 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n\nx : three\n============================\nx = One \\/ x = Two \\/ x = Three",
          "tactic": "intros x"
      },
      {
          "before": "1 Goal Total\n\t1 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n\nx : three\n============================\nx = One \\/ x = Two \\/ x = Three",
          "after": "3 Goals Total\n\t3 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n\n============================\nOne = One \\/ One = Two \\/ One = Three\n\n\n============================\nTwo = One \\/ Two = Two \\/ Two = Three\n\n\n============================\nThree = One \\/ Three = Two \\/ Three = Three",
          "tactic": "destruct x"
      },
      {
          "before": "3 Goals Total\n\t3 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n\n============================\nOne = One \\/ One = Two \\/ One = Three\n\n\n============================\nTwo = One \\/ Two = Two \\/ Two = Three\n\n\n============================\nThree = One \\/ Three = Two \\/ Three = Three",
          "after": "2 Goals Total\n\t2 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n\n============================\nTwo = One \\/ Two = Two \\/ Two = Three\n\n\n============================\nThree = One \\/ Three = Two \\/ Three = Three",
          "tactic": "left; reflexivity"
      },
      {
          "before": "2 Goals Total\n\t2 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n\n============================\nTwo = One \\/ Two = Two \\/ Two = Three\n\n\n============================\nThree = One \\/ Three = Two \\/ Three = Three",
          "after": "1 Goal Total\n\t1 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n\n============================\nThree = One \\/ Three = Two \\/ Three = Three",
          "tactic": "right; left; reflexivity"
      },
      {
          "before": "1 Goal Total\n\t1 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n\n============================\nThree = One \\/ Three = Two \\/ Three = Three",
          "after": "0 Goal Total\n\t0 focused; 0 unfocused ([]); 0 shelved; 0 admitted\n\n",
          "tactic": "right; right; reflexivity"
      }
  ]

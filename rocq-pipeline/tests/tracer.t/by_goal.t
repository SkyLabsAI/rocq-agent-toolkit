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
          "action": "exact I.",
          "before": [
              "\n============================\nTrue"
          ],
          "after": [],
          "info": null
      }
  ]
  [
      {
          "action": "exact ((fun (H : P) => H)).",
          "before": [
              "\nP : Prop\n============================\nP -> P"
          ],
          "after": [],
          "info": null
      }
  ]
  [
      {
          "action": "trivial.",
          "before": [
              "\n============================\n5 <= 5"
          ],
          "after": [],
          "info": null
      }
  ]
  [
      {
          "action": "exact ((eq_refl _)).",
          "before": [
              "\n============================\n5 = 5"
          ],
          "after": [],
          "info": null
      }
  ]
  [
      {
          "action": "exact I.",
          "before": [
              "\n============================\nTrue"
          ],
          "after": [],
          "info": null
      }
  ]
  [
      {
          "action": "exact ((fun (H : P) => H)).",
          "before": [
              "\nP : Prop\n============================\nP -> P"
          ],
          "after": [],
          "info": null
      }
  ]
  [
      {
          "action": "trivial.",
          "before": [
              "\n============================\n5 <= 5"
          ],
          "after": [],
          "info": null
      }
  ]
  [
      {
          "action": "exact ((eq_refl _)).",
          "before": [
              "\n============================\n5 = 5"
          ],
          "after": [],
          "info": null
      }
  ]
  [
      {
          "action": "exact (I).",
          "before": [
              "\n============================\nTrue"
          ],
          "after": [],
          "info": null
      }
  ]
  [
      {
          "action": "exact ((eq_refl _)).",
          "before": [
              "\n============================\n5 = 5"
          ],
          "after": [],
          "info": null
      }
  ]
  [
      {
          "action": "intros x.",
          "before": [
              "\n============================\nforall x : three, x = One \\/ x = Two \\/ x = Three"
          ],
          "after": [
              "\nx : three\n============================\nx = One \\/ x = Two \\/ x = Three"
          ],
          "info": null
      },
      {
          "action": "destruct x.",
          "before": [
              "\nx : three\n============================\nx = One \\/ x = Two \\/ x = Three"
          ],
          "after": [
              "\n============================\nOne = One \\/ One = Two \\/ One = Three",
              "\n============================\nTwo = One \\/ Two = Two \\/ Two = Three",
              "\n============================\nThree = One \\/ Three = Two \\/ Three = Three"
          ],
          "info": null
      },
      {
          "action": "left; reflexivity.",
          "before": [
              "\n============================\nOne = One \\/ One = Two \\/ One = Three",
              "\n============================\nTwo = One \\/ Two = Two \\/ Two = Three",
              "\n============================\nThree = One \\/ Three = Two \\/ Three = Three"
          ],
          "after": [
              "\n============================\nTwo = One \\/ Two = Two \\/ Two = Three",
              "\n============================\nThree = One \\/ Three = Two \\/ Three = Three"
          ],
          "info": null
      },
      {
          "action": "right; left; reflexivity.",
          "before": [
              "\n============================\nTwo = One \\/ Two = Two \\/ Two = Three",
              "\n============================\nThree = One \\/ Three = Two \\/ Three = Three"
          ],
          "after": [
              "\n============================\nThree = One \\/ Three = Two \\/ Three = Three"
          ],
          "info": null
      },
      {
          "action": "right; right; reflexivity.",
          "before": [
              "\n============================\nThree = One \\/ Three = Two \\/ Three = Three"
          ],
          "after": [],
          "info": null
      }
  ]

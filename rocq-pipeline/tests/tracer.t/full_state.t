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
  $ uv run rat trace --tracer rocq_pipeline.tracers.json_goal:build_full_state --task-file tasks.yaml
  

  $ LC_ALL=C ls *.json | xargs -n 1 python3 -m json.tool
  [
      {
          "before": [
              {
                  "hyps": [],
                  "goal": "(forall x : three, x = One \\/ x = Two \\/ x = Three)"
              }
          ],
          "after": [
              {
                  "hyps": [
                      {
                          "name": "x",
                          "type": "three"
                      }
                  ],
                  "goal": "(x = One \\/ x = Two \\/ x = Three)"
              }
          ],
          "tactic": "intros x"
      },
      {
          "before": [
              {
                  "hyps": [
                      {
                          "name": "x",
                          "type": "three"
                      }
                  ],
                  "goal": "(x = One \\/ x = Two \\/ x = Three)"
              }
          ],
          "after": [
              {
                  "hyps": [],
                  "goal": "(One = One \\/ One = Two \\/ One = Three)"
              },
              {
                  "hyps": [],
                  "goal": "(Two = One \\/ Two = Two \\/ Two = Three)"
              },
              {
                  "hyps": [],
                  "goal": "(Three = One \\/ Three = Two \\/ Three = Three)"
              }
          ],
          "tactic": "destruct x"
      },
      {
          "before": [
              {
                  "hyps": [],
                  "goal": "(One = One \\/ One = Two \\/ One = Three)"
              },
              {
                  "hyps": [],
                  "goal": "(Two = One \\/ Two = Two \\/ Two = Three)"
              },
              {
                  "hyps": [],
                  "goal": "(Three = One \\/ Three = Two \\/ Three = Three)"
              }
          ],
          "after": [
              {
                  "hyps": [],
                  "goal": "(Two = One \\/ Two = Two \\/ Two = Three)"
              },
              {
                  "hyps": [],
                  "goal": "(Three = One \\/ Three = Two \\/ Three = Three)"
              }
          ],
          "tactic": "left; reflexivity"
      },
      {
          "before": [
              {
                  "hyps": [],
                  "goal": "(Two = One \\/ Two = Two \\/ Two = Three)"
              },
              {
                  "hyps": [],
                  "goal": "(Three = One \\/ Three = Two \\/ Three = Three)"
              }
          ],
          "after": [
              {
                  "hyps": [],
                  "goal": "(Three = One \\/ Three = Two \\/ Three = Three)"
              }
          ],
          "tactic": "right; left; reflexivity"
      },
      {
          "before": [
              {
                  "hyps": [],
                  "goal": "(Three = One \\/ Three = Two \\/ Three = Three)"
              }
          ],
          "after": [],
          "tactic": "right; right; reflexivity"
      }
  ]

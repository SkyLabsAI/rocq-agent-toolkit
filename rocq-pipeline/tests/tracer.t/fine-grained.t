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

  $ cat > demo.v <<EOF
  > Lemma add_S : forall a b, a + S b = S (a + b).
  > Proof.
  >   induction a; simpl; auto.
  > Qed.
  > EOF

  $ uv run rat trace --fine-grained --tracer rocq_pipeline.tracers.string_goal --task-json '{"file": "demo.v", "locator": "Lemma:add_S" }'
  

  $ LC_ALL=C ls *.json | sort
  demo.v_Lemma:add_S.json

  $ LC_ALL=C ls *.json | sort | xargs -n 1 python3 -m json.tool
  [
      {
          "action": "induction a.",
          "before": [
              "\n============================\nforall a b : nat, a + S b = S (a + b)"
          ],
          "after": [
              "\n============================\nforall b : nat, 0 + S b = S (0 + b)",
              "\na : nat\nIHa : forall b : nat, a + S b = S (a + b)\n============================\nforall b : nat, S a + S b = S (S a + b)"
          ],
          "info": null
      },
      {
          "action": "simpl.",
          "before": [
              "\n============================\nforall b : nat, 0 + S b = S (0 + b)",
              "\na : nat\nIHa : forall b : nat, a + S b = S (a + b)\n============================\nforall b : nat, S a + S b = S (S a + b)"
          ],
          "after": [
              "\n============================\nforall b : nat, S b = S b",
              "\na : nat\nIHa : forall b : nat, a + S b = S (a + b)\n============================\nforall b : nat, S a + S b = S (S a + b)"
          ],
          "info": null
      },
      {
          "action": "simpl.",
          "before": [
              "\n============================\nforall b : nat, S b = S b",
              "\na : nat\nIHa : forall b : nat, a + S b = S (a + b)\n============================\nforall b : nat, S a + S b = S (S a + b)"
          ],
          "after": [
              "\n============================\nforall b : nat, S b = S b",
              "\na : nat\nIHa : forall b : nat, a + S b = S (a + b)\n============================\nforall b : nat, S (a + S b) = S (S (a + b))"
          ],
          "info": null
      },
      {
          "action": "auto.",
          "before": [
              "\n============================\nforall b : nat, S b = S b",
              "\na : nat\nIHa : forall b : nat, a + S b = S (a + b)\n============================\nforall b : nat, S (a + S b) = S (S (a + b))"
          ],
          "after": [
              "\na : nat\nIHa : forall b : nat, a + S b = S (a + b)\n============================\nforall b : nat, S (a + S b) = S (S (a + b))"
          ],
          "info": null
      },
      {
          "action": "auto.",
          "before": [
              "\na : nat\nIHa : forall b : nat, a + S b = S (a + b)\n============================\nforall b : nat, S (a + S b) = S (S (a + b))"
          ],
          "after": [],
          "info": null
      },
      {
          "action": "induction a; simpl; auto.",
          "before": [
              "\n============================\nforall a b : nat, a + S b = S (a + b)"
          ],
          "after": [],
          "info": null
      }
  ]

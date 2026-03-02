  $ cp $TESTDIR/tasks.yaml .
  $ cat tasks.yaml
  project:
    name: rocq_pipeline_test
    git_url: dummy
    git_commit: dummy
    path: .
  tasks:
  - file: theories/my_nat.v
    locator: Lemma:zero_add
    tags:
    - NumTactics=1
    - proof
    - qed
    - reflexivity
  - file: theories/test_simple.v
    locator: Lemma:is_true
    tags:
    - NumTactics=1
    - proof
    - qed
    - trivial
  $ rat filter --output with_mod1.yaml \
  >   --rename-task '$I-no-hints' \
  >   --add-mod '{"insert_command":{"commands": ["MOD1."], "ghost": true}}' \
  >   tasks.yaml
  Returned 2 of 2 tasks.

  $ cat with_mod1.yaml
  project_bundles:
  - project:
      name: rocq_pipeline_test
      git_url: dummy
      git_commit: dummy
      path: .
    tasks:
    - name: theories/my_nat.v#Lemma:zero_add-no-hints
      file: theories/my_nat.v
      locator: Lemma:zero_add
      tags:
      - NumTactics=1
      - proof
      - qed
      - reflexivity
      modifiers:
      - insert_command:
          commands:
          - MOD1.
    - name: theories/test_simple.v#Lemma:is_true-no-hints
      file: theories/test_simple.v
      locator: Lemma:is_true
      tags:
      - NumTactics=1
      - proof
      - qed
      - trivial
      modifiers:
      - insert_command:
          commands:
          - MOD1.

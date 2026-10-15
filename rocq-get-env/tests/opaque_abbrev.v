Require Import skylabs_ai.tools.get_env.plugin.

Lemma target : True.
Proof. exact I. Qed.

Abbreviation alias := target.

Print JSON Environment get_env.tests.opaque_abbrev.

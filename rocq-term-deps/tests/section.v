Require Import skylabs_ai.tools.term_deps.plugin.
Section junk.
  Context (k m n : nat).
  Definition f := k + m + n.
  DepsOfJSON f.
  DepsOfJSON term_deps.tests.section.junk.f.
  Definition g := f + k.
  DepsOfJSON term_deps.tests.section.junk.g.
End junk.
DepsOfJSON f.
DepsOfJSON term_deps.tests.section.f.
DepsOfJSON term_deps.tests.section.g.

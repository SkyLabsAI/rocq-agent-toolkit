Require Import skylabs_ai.tools.term_deps.plugin.
Fail DepsOf nat.
DepsOf Nat.add.
Definition weird (x y : nat) := x + (y * 2) + 1.
DepsOf weird.

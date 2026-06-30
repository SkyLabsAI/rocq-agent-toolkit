(** Ltac2 surface of the [rocq-term-deps] plugin. *)
Require Export skylabs_ai.tools.term_deps.plugin.
From Ltac2 Require Import Ltac2.

(** [term_deps t] returns the *immediate* dependencies of the single term [t] as
    a pair [(inductive_names, constant_names)] of absolute-name strings.

    Notes:
    - Dependencies are *syntactic / immediate*: a constant occurring in [t] is
      reported as-is; its body is NOT unfolded (so this is not transitive).
    - [Var], [Rel] and [Evar] nodes are ignored, so it is safe on open terms.
    - The result is plain structured data: callers can union it over several
      terms, build a JSON object (e.g. with [ltac2-json]), or resolve the names
      back to references with [Ltac2.Env.get] / [Env.expand]. *)
Ltac2 @ external term_deps : constr -> string list * string list :=
  "rocq-term-deps" "term_deps".

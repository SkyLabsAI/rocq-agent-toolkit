The [term_deps] Ltac2 external computes the immediate (syntactic) inductive and
constant dependencies of an arbitrary term — not just a defined constant — and
returns them as plain structured data (string lists).

  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ cat > test.v <<EOF
  > Require Import skylabs_ai.tools.term_deps.TermDeps.
  > From Ltac2 Require Import Ltac2.
  > Ltac2 show (t : constr) : unit :=
  >   let (inds, consts) := term_deps t in
  >   Message.print (Message.of_string (String.concat ""
  >     ["inductives: "; String.concat ", " inds;
  >      " | constants: "; String.concat ", " consts])).
  > (* a single closed term *)
  > Ltac2 Eval show constr:(1 + 2 * 3).
  > (* a term with a bound variable (the Rel is ignored) *)
  > Ltac2 Eval show constr:(fun n : nat => n + 0).
  > (* immediate, NOT transitive: [foo] is reported, its body is not unfolded
  >    (so [Nat.add], used only inside [foo], does not appear) *)
  > Definition foo (n : nat) := n + 2.
  > Ltac2 Eval show constr:(foo 3).
  > (* a free (section) variable is ignored; the surrounding constants are kept *)
  > Section S.
  >   Variable y : nat.
  >   Ltac2 Eval show constr:(y + foo y).
  > End S.
  > EOF

  $ rocq compile test.v
  inductives: Corelib.Init.Datatypes.nat | constants: Corelib.Init.Nat.mul, Corelib.Init.Nat.add
  - : unit = ()
  inductives: Corelib.Init.Datatypes.nat | constants: Corelib.Init.Nat.add
  - : unit = ()
  inductives: Corelib.Init.Datatypes.nat | constants: test.foo
  - : unit = ()
  inductives:  | constants: Corelib.Init.Nat.add, test.foo
  - : unit = ()

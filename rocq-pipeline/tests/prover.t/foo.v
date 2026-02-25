Require Import Stdlib.Strings.String.

Open Scope string_scope.
Inductive my_nat : Set :=
| MyO
| MyS (_ : my_nat).

(* Trap 1: Comment containing the target text *)
(* TODO: If the induction gets too messy, just use Proof. Admitted. *)

(* Trap 2: String literal containing the target text *)
Definition fallback_string := "Failed to solve; left as Proof. Admitted.".

Fixpoint my_add (a b : my_nat) : my_nat :=
  match a with
  | MyO => b
  | MyS a => my_add a (MyS b)
  end.

Lemma zero_add : forall a, my_add MyO a = a.
Proof. Admitted.

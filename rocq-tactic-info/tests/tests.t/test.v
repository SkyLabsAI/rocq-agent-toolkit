Require Import skylabs.tactic_info.explain.

info.Ltac (intros; intros).
info.Ltac (intro H; apply _).
info.Ltac (intro; [ intro | intros | apply _ ]).
info.Ltac (solve [ intro | apply _ ]).
info.Ltac (intro; [ intro | apply _ ]).
info.Ltac (intro; [ intro .. | apply _ ]).
info.Ltac (intro; [ intro; apply _ .. | | apply _ ]).
info.Ltac (progress intro).
info.Ltac (match goal with | _ => idtac end).

Ltac nothing := idtac.

info.Ltac (first [ idtac | apply _ | nothing ]).
info.Ltac (solve [ idtac | auto | nothing ]).
info.Ltac (fail).
info.Ltac (idtac "T").

Goal forall x y : unit, True.
Proof.
    info.Ltac (intro x; intro y; trivial).
    info.Ltac (intros; trivial).
    intros x y.
    info.Ltac (generalize x; trivial).
    info.Ltac (assert True; [ trivial | assumption ]).
    trivial.
Qed.

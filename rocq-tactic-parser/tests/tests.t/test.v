Require Import skylabs_ai.tactic_parser.explain.

Explain (intros; intros).
Explain (intro H; apply _).
Explain (intro; [ intro | intros | apply _ ]).
Explain (solve [ intro | apply _ ]).
Explain (intro; [ intro | apply _ ]).
Explain (intro; [ intro .. | apply _ ]).
Explain (intro; [ intro; apply _ .. | | apply _ ]).
Explain (progress intro).
Explain (match goal with | _ => idtac end).

Ltac nothing := idtac.

Explain (first [ idtac | apply _ | nothing ]).
Explain (solve [ idtac | auto | nothing ]).
Explain (fail).
Explain (idtac "T").

Goal forall x y : unit, True.
Proof.
    Explain (intro x; intro y; trivial).
    Explain (intros; trivial).
    intros x y.
    Explain (generalize x; trivial).
    Explain (assert True; [ trivial | assumption ]).
    trivial.
Qed.

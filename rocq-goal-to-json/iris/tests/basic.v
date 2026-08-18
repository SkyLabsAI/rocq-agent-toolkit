Require Import skylabs_ai.extractors.goal_to_json.iris.goal_util.
Require Import iris.proofmode.proofmode.

Goal True.
Proof. goal_to_json. trivial. Abort.

Goal True -> True.
Proof. goal_to_json. Abort.

Goal let x : True := I in False.
Proof.
  goal_to_json.
  intros.
  goal_to_json.
Abort.

Goal forall a b : Prop, a -> a /\ b.
Proof.
  goal_to_json.
  intro.
  goal_to_json.
  intro.
  goal_to_json.
  intro HH.
  goal_to_json.
Abort.

Section with_PROP.
  Variable PROP : bi.
  Variable P : PROP.

  Goal P ⊢ P ∗ emp.
  Proof.
    goal_to_json.
    iStartProof.
    goal_to_json.
    iIntros "H".
    goal_to_json.
    iSplitL.
    all: goal_to_json.
    1: goal_to_json.
    2: goal_to_json.
    1,2: goal_to_json.
    2,1: goal_to_json.
    1:{ goal_to_json. iFrame. }
    goal_to_json.
  Abort.
End with_PROP.

Require Import skylabs_ai.extractors.goal_to_json.basic.goal_util.

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
  split.
  all: goal_to_json.
  1: goal_to_json.
  2: goal_to_json.
  1,2: goal_to_json.
  2,1: goal_to_json.
  goal_to_json.
  auto.
  goal_to_json.
Abort.

Goal forall a b : Prop, a -> a /\ b.
Proof.
  goal_to_json.
  intros.
  goal_to_json.
  split.
  goal_to_json.
  { goal_to_json.
    auto. }
  { goal_to_json.
    auto.
    goal_to_json.
Abort.

Goal forall a b : Prop, a -> a /\ b.
Proof.
  intros; split.
  goal_to_json.
  1: goal_to_json.
  2: goal_to_json.
  Focus 1.
  goal_to_json.
  auto.
  goal_to_json.
Abort.

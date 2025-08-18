Inductive tree {A B : Type} : Type := node : A -> forest -> tree

with forest {A B : Type} : Type :=
| leaf : B -> forest
| cons : tree -> forest -> forest.

Arguments tree : clear implicits.
Arguments forest : clear implicits.

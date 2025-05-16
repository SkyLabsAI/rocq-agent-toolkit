Require Import skylabs_ai.ltac2_json.JSON.
Require Import Ltac2.Ltac2.

Ltac2 Derive List.

Ltac2 Type variant := [ VariantA | VariantB | VariantC ].

Ltac2 Derive json For variant.
Print Ltac2 variant_to_json.

Ltac2 Type point := { x : int; y : int; z : int; }.

Ltac2 Derive json For point.
Print Ltac2 point_to_json.

Ltac2 Type triple := int list * bool * int.

Ltac2 Derive json For triple.
Print Ltac2 triple_to_json.

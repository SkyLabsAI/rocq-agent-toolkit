Require Import skylabs_ai.ltac2_derive.derive.
Require Import Ltac2.Ltac2.

Set Warnings "-ltac2-unused-variable".

Ltac2 Derive List.

Ltac2 Type variant := [ VariantA | VariantB | VariantC ].

Ltac2 Derive pp, eq For variant.

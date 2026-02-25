Require Import ssreflect.

Set Default Goal Selector "!".
Set SsrIdents.
Goal True.
Proof. Admitted.

Set Default Goal Selector "1".
Set SsrIdents.
Goal True.
Proof. Admitted.

Set Default Goal Selector "1".
Unset SsrIdents.
Goal True.
Proof. Admitted.

Set Default Goal Selector "!".
Unset SsrIdents.
Goal True.
Proof. Admitted.

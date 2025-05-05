Declare ML Module "ltac2-json.plugin".

Require Import Ltac2.Ltac2.

Ltac2 Type rec t := [
  | Null
  | Bool(bool)
  | Int(int)
  | Intlit(string)
  | Float(float)
  | String(string)
  | Assoc((string * t) list)
  | List(t list)
  | Tuple(t list)
  | Variant(string * t option)
].

Ltac2 Type json := t.

Ltac2 @ external to_string : t -> string :=
  "ltac2-json" "to_string".

Ltac2 @ external of_string : string -> t option :=
  "ltac2-json" "of_string".

Require Import Ltac2.Ltac2.
Require Import skylabs_ai.ltac2_derive.derive.

Declare ML Module "ltac2-json.plugin".

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
  | Variant(string, t option)
].

Ltac2 Type json := t.

Ltac2 @ external to_string : t -> string :=
  "ltac2-json" "to_string".

Ltac2 @ external of_string : string -> t option :=
  "ltac2-json" "of_string".

Ltac2 int_to_json : int -> json := fun i =>
  Int(i).

Ltac2 bool_to_json : bool -> json := fun b =>
  Bool(b).

Ltac2 option_to_json : ('a -> json) -> 'a option -> json := fun f o =>
  match o with
  | None => Null
  | Some(v) => f v
  end.

Ltac2 list_to_json : ('a -> json) -> 'a list -> json := fun f l =>
  List(List.map f l).

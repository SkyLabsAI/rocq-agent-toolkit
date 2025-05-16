open Ltac2_plugin
open Tac2ffi
open Tac2externals

module JSON = struct
  type t = Yojson.Safe.t

  let to_string : t -> string = fun json ->
    Yojson.Safe.pretty_to_string ~std:true json

  let of_string : string -> t option = fun s ->
    try Some(Yojson.Safe.from_string s) with Yojson.Json_error(_) -> None
end

let define s =
  define Tac2expr.{ mltac_plugin = "ltac2-json"; mltac_tactic = s }

let of_json : JSON.t -> Tac2val.valexpr = fun json ->
  let rec of_json json =
    let of_block1 n v = of_block (n, [|v|]) in
    let of_block2 n v1 v2 = of_block (n, [|v1; v2|]) in
    match json with
    | `Null         -> of_int 0
    | `Bool(b)      -> of_block1 0 (of_bool b)
    | `Int(i)       -> of_block1 1 (of_int i)
    | `Intlit(s)    -> of_block1 2 (of_string s)
    | `Float(f)     -> of_block1 3 (of_float (Float64.of_float f))
    | `String(s)    -> of_block1 4 (of_string s)
    | `Assoc(l)     -> of_block1 5 (of_list (of_pair of_string of_json) l)
    | `List(l)      -> of_block1 6 (of_list of_json l)
    | `Tuple(l)     -> of_block1 7 (of_list of_json l)
    | `Variant(s,o) -> of_block2 8 (of_string s) (of_option of_json o)
  in
  of_json json

let to_json : Tac2val.valexpr -> JSON.t = fun v ->
  let rec to_json v =
    if Tac2val.Valexpr.is_int v then `Null else
    match to_block v with
    | (0, [|v|]     ) -> `Bool(to_bool v)
    | (1, [|v|]     ) -> `Int(to_int v)
    | (2, [|v|]     ) -> `Intlit(to_string v)
    | (3, [|v|]     ) -> `Float(Float64.to_float (to_float v))
    | (4, [|v|]     ) -> `String(to_string v)
    | (5, [|v|]     ) -> `Assoc(to_list (to_pair to_string to_json) v)
    | (6, [|v|]     ) -> `List(to_list to_json v)
    | (7, [|v|]     ) -> `Tuple(to_list to_json v)
    | (8, [|v1; v2|]) -> `Variant(to_string v1, to_option to_json v2)
    | (_, _         ) -> assert false
  in
  to_json v

let json : JSON.t repr = make_repr of_json to_json

let _ =
  define "to_string" (json @-> ret string) JSON.to_string;
  define "of_string" (string @-> ret (option json)) JSON.of_string

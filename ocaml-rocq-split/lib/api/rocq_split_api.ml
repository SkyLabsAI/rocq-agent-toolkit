let json_error error =
  let json =
    `Assoc([
      ("error", `String(error));
      ("loc"  , `Null         );
    ])
  in
  Yojson.Safe.pretty_to_string ~std:true json

let get_raw : args:string list -> file:string -> (string, string) result =
    fun ~args ~file ->
  let args = Array.of_list ("rocq_split" :: args @ ["-topfile"; file; file]) in
  let err s = Error(json_error s) in
  try
    let ic = Unix.open_process_args_in "rocq_split" args in
    let data = In_channel.input_all ic in
    match Unix.close_process_in ic with
    | Unix.WEXITED(0) -> Ok(data)
    | Unix.WEXITED(1) -> Error(data)
    | _               -> err "The [rocq_split] command exited abnormally."
  with
  | Unix.Unix_error(_,_,_) ->
      err "A system call failed in the [rocq_split] API."
  | Sys_error(_)           ->
      err "A system error occured in the [rocq_split] API."

type json = Yojson.Safe.t

let get_json : args:string list -> file:string -> (json, json) result =
    fun ~args ~file ->
  let parse_json s =
    try Yojson.Safe.from_string s with
    | Yojson.Json_error(_) -> assert false (* Should be impossible. *)
  in
  match get_raw ~args ~file with
  | Error(s) -> Error(parse_json s)
  | Ok(s)    -> Ok(parse_json s)

type sentence = Rocq_split.sentence = {
  kind : string;
  text : string;
  bp : int;
  ep : int;
}

type error = {
  message : string;
  loc : Rocq_loc.t option;
}

let get : args:string list -> file:string -> (sentence list, error) result =
    fun ~args ~file ->
  let to_error json =
    let fields =
      match json with
      | `Assoc(fields) -> fields
      | _              -> assert false (* Unreachable. *)
    in
    let message =
      match List.assoc_opt "error" fields with
      | Some(`String(error)) -> error
      | _                    -> assert false (* Unreachable. *)
    in
    let loc_of_json json =
      match Rocq_loc.of_yojson json with
      | Ok(loc)  -> loc
      | Error(_) -> assert false (* Unreachable. *)
    in
    let loc =
      match List.assoc_opt "loc" fields with
      | Some(`Null) -> None
      | Some(json ) -> Some(loc_of_json json)
      | _           -> assert false (* Unreachable. *)
    in
    {message; loc}
  in
  let to_sentence item =
    match Rocq_split.sentence_of_yojson item with
    | Ok(s)    -> s
    | Error(_) -> assert false (* Unreachable. *)
  in
  let to_sentences json =
    let fields =
      match json with
      | `Assoc(fields) -> fields
      | _              -> assert false (* Unreachable. *)
    in
    let items =
      match List.assoc_opt "items" fields with
      | Some(`List(items)) -> items
      | _                  -> assert false (* Unreachable. *)
    in
    List.map to_sentence items
  in
  match get_json ~args ~file with
  | Error(json) -> Error(to_error json)
  | Ok(json)    -> Ok(to_sentences json)

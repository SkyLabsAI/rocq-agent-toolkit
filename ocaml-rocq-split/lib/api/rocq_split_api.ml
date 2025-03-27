let get_raw : args:string list -> file:string -> (string, string) result =
    fun ~args ~file ->
  let args = Array.of_list ("rocq_split" :: args @ ["-topfile"; file; file]) in
  try
    let ic = Unix.open_process_args_in "rocq_split" args in
    let data = In_channel.input_all ic in
    match Unix.close_process_in ic with
    | Unix.WEXITED(0) -> Ok(data)
    | _               -> Error("rocq_split exited abnormally")
  with
  | Unix.Unix_error(_,_,_) -> Error("system call failed")
  | Sys_error(_)           -> Error("system error")

type json = Yojson.Safe.t

let get_json : args:string list -> file:string -> (json, string) result =
    fun ~args ~file ->
  match get_raw ~args ~file with Error(s) -> Error(s) | Ok(s) ->
  try Ok(Yojson.Safe.from_string s) with Yojson.Json_error(s) -> Error(s)

type sentence = Rocq_split.sentence = {
  kind : string;
  text : string;
  bp : int;
  ep : int;
}

let get : args:string list -> file:string -> (sentence list, string) result =
    fun ~args ~file ->
  match get_json ~args ~file with Error(s) -> Error(s) | Ok(json) ->
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
  let to_sentence item =
    match Rocq_split.sentence_of_yojson item with
    | Ok(s)    -> s
    | Error(_) -> assert false (* Unreachable. *)
  in
  Ok(List.map to_sentence items)

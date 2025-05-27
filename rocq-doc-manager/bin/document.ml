type sid = Rocq_toplevel.StateId.t

type processed =
  | Blanks of {index : int; off : int; text : string}
  | Command of {index : int; off : int; sid_before : sid; text : string}

type unprocessed =
  | RemBlanks of {text : string}
  | RemCommand of {text : string}

type t = {
  args : string list;
  file : string;
  toplevel : Rocq_toplevel.t;
  mutable rev_prefix : processed list;
  mutable cursor_sid : sid;
  mutable cursor_off : int;
  mutable suffix : unprocessed list;
}

let file : t -> string = fun d ->
  d.file

let next_index : t -> int = fun d ->
  match d.rev_prefix with
  | []                       -> 0
  | Blanks({index; _})  :: _ -> index + 1
  | Command({index; _}) :: _ -> index + 1

let init : args:string list -> file:string -> t = fun ~args ~file ->
  let toplevel = Rocq_toplevel.init ~args ~file in
  let cursor_sid = Rocq_toplevel.get_state_id toplevel in
  let cursor_off = 0 in
  let (rev_prefix, suffix) = ([], []) in
  {args; file; toplevel; rev_prefix; cursor_sid; cursor_off; suffix}

let stop : t -> unit = fun d ->
  Rocq_toplevel.stop d.toplevel

let to_unprocessed : Rocq_split_api.sentence -> unprocessed = fun s ->
  let text = s.Rocq_split_api.text in
  match s.Rocq_split_api.kind with
  | "blanks" -> RemBlanks({text})
  | _        -> RemCommand({text})

let load_file : t -> (unit, string) result = fun d ->
  let {file; args; _} = d in
  match Rocq_split_api.get ~args ~file with
  | Error(s)      -> Error(s)
  | Ok(sentences) ->
  let suffix = List.rev_map to_unprocessed sentences in
  d.suffix <- List.rev_append suffix d.suffix;
  Ok(())

type loc = Rocq_loc.t option

let loc_to_yojson loc =
  match loc with
  | None      -> `Null
  | Some(loc) -> Rocq_loc.to_json loc

let loc_of_yojson json =
  match json with
  | `Null -> Ok(None)
  | _     -> Result.map (fun o -> Some(o)) (Rocq_loc.of_json json)

let loc_to_json = loc_to_yojson

type command_data = Rocq_toplevel.run_data = {
  open_subgoals : string option;
  new_constants : (string list [@default []]);
  removed_constants : (string list [@default []]);
  new_inductives : (string list [@default []]);
  removed_inductives : (string list [@default []]);
}
[@@deriving yojson]

let command_data_to_json = command_data_to_yojson

let insert_blanks : t -> text:string -> unit = fun d ~text ->
  let len = String.length text in
  if len = 0 then () else
  match d.rev_prefix with
  | Blanks({index; off; text = blanks}) :: rev_prefix ->
      let text = blanks ^ text in
      d.rev_prefix <- Blanks({index; off; text}) :: rev_prefix;
      d.cursor_off <- d.cursor_off + len
  | _                                                 ->
      let index = next_index d in
      let off = d.cursor_off in
      d.rev_prefix <- Blanks({index; off; text}) :: d.rev_prefix;
      d.cursor_off <- d.cursor_off + len

let insert_command : t -> text:string ->
    (command_data, loc * string) result = fun d ~text ->
  let off = d.cursor_off in
  let sid_before = d.cursor_sid in
  let res = Rocq_toplevel.run d.toplevel ~off ~text in
  match res with Error(_) -> res | _ ->
  let index = next_index d in
  d.rev_prefix <- Command({index; off; sid_before; text}) :: d.rev_prefix;
  d.cursor_sid <- Rocq_toplevel.get_state_id d.toplevel;
  d.cursor_off <- d.cursor_off + String.length text;
  res

let revert_before : t -> index:int -> unit = fun d ~index:i ->
  let cur_index = next_index d in
  if i < 0 || cur_index <= i then invalid_arg "Document.revert_before";
  let rec revert rev_prefix suffix sid =
    match rev_prefix with
    | Blanks({index; text; _})              :: rev_prefix ->
        let suffix = RemBlanks({text}) :: suffix in
        if index = i then
          (rev_prefix, suffix, sid)
        else
          revert rev_prefix suffix sid
    | Command({index; sid_before; text; _}) :: rev_prefix ->
        let suffix = RemCommand({text}) :: suffix in
        if index = i then
          (rev_prefix, suffix, sid_before)
        else
          revert rev_prefix suffix sid_before
    | []                                                  ->
        assert false (* Unreachable. *)
  in
  let (rev_prefix, suffix, sid) = revert d.rev_prefix d.suffix d.cursor_sid in
  d.rev_prefix <- rev_prefix;
  d.suffix <- suffix;
  match Rocq_toplevel.back_to d.toplevel ~sid with
  | Ok(())   -> ()
  | Error(_) -> assert false (* Unreachable. *)

let clear_suffix : t -> unit = fun d ->
  d.suffix <- []

type byte_loc = {off : int; len : int}

let byte_loc_of_last_step : t -> byte_loc option = fun d ->
  match d.rev_prefix with [] -> None
  | Blanks({off; text; _})  :: _
  | Command({off; text; _}) :: _ ->
      Some({off; len = String.length text})

let run_step : t -> (command_data option, loc * string) result = fun d ->
  match d.suffix with
  | []             -> Error(None, "no step left to run")
  | step :: suffix ->
  d.suffix <- suffix;
  match step with
  | RemBlanks({text})  -> insert_blanks d ~text; Ok(None)
  | RemCommand({text}) ->
      Result.map (fun d -> Some(d)) (insert_command d ~text)

type processed_item = {
  index : int;
  kind : [`Blanks | `Command];
  off : int;
  text : string;
}

let last_processed_item : t -> processed_item option = fun d ->
  match d.rev_prefix with
  | Blanks({index; off; text}) :: _     ->
      Some({index; kind = `Blanks; off; text})
  | Command({index; off; text; _}) :: _ ->
      Some({index; kind = `Command; off; text})
  | []                                  ->
      None

let doc_prefix : t -> (kind:string -> off:int -> text:string -> 'a)
     -> 'a list = fun d f ->
  let rec build acc rev_prefix =
    match rev_prefix with
    | []                                    -> acc
    | Blanks({off; text; _})  :: rev_prefix ->
        build (f ~kind:"blanks" ~off ~text :: acc) rev_prefix
    | Command({off; text; _}) :: rev_prefix ->
        build (f ~kind:"command" ~off ~text :: acc) rev_prefix
  in
  build [] d.rev_prefix

let doc_suffix : t -> (kind:string -> text:string -> 'a)
    -> 'a list = fun d f ->
  let rec build suffix =
    match suffix with
    | []                           -> []
    | RemBlanks({text})  :: suffix ->
        f ~kind:"blanks"  ~text :: build suffix
    | RemCommand({text}) :: suffix ->
        f ~kind:"command" ~text :: build suffix
  in
  build d.suffix

let has_suffix : t -> bool = fun d ->
  d.suffix <> []

let commit : t -> include_suffix:bool -> unit = fun d ~include_suffix ->
  Out_channel.with_open_text d.file @@ fun oc ->
  let output_processed p =
    match p with Blanks({text; _}) | Command({text; _}) ->
    Out_channel.output_string oc text
  in
  List.iter output_processed (List.rev d.rev_prefix);
  let output_unprocessed u =
    match u with RemBlanks({text}) | RemCommand({text}) ->
    Out_channel.output_string oc text
  in
  if include_suffix then List.iter output_unprocessed d.suffix

let read_file file =
  let buf = Buffer.create 73 in
  let ic = open_in file in
  try while true do
    Buffer.add_string buf (input_line ic);
    Buffer.add_char buf '\n'
  done; assert false with End_of_file -> Buffer.contents buf

let compile : t -> (unit, string) result * string * string = fun d ->
  let args = "c" :: d.args @ [d.file] in
  let stdout = d.file ^ ".stdout" in
  let stderr = d.file ^ ".stderr" in
  let cmd = Filename.quote_command "rocq" ~stdout ~stderr args in
  let ret =
    match Unix.system cmd with
    | Unix.WEXITED(0)   -> Ok(())
    | Unix.WEXITED(i)   -> Error(Format.sprintf "Exited with code %i." i)
    | Unix.WSIGNALED(i) -> Error(Format.sprintf "Killed with signal %i." i)
    | Unix.WSTOPPED(i)  -> Error(Format.sprintf "Stopped by signal %i." i)
  in
  let out = read_file stdout in
  Sys.remove stdout;
  let err = read_file stderr in
  Sys.remove stderr;
  (ret, out, err)

type feedback = Rocq_toplevel.feedback = {
  kind : [`Debug | `Info | `Notice | `Warning | `Error];
  text : string;
  loc  : loc;
}
[@@deriving yojson]

let feedback_to_json = feedback_to_yojson

let get_feedback : t -> feedback list = fun d ->
  try Rocq_toplevel.get_feedback d.toplevel with
  | Rocq_toplevel.No_feedback -> []

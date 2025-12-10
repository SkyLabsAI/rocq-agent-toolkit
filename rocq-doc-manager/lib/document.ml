type sid = Rocq_toplevel.StateID.t

type processed =
  | Blanks of {index : int; off : int; text : string}
  | Command of {index : int; off : int; text : string}
  | Ghost of {index : int; off : int; text : string}

type unprocessed =
  | RemBlanks of {text : string}
  | RemCommand of {text : string}
  | RemGhost of {text : string}

type in_toplevel = {
  processed : processed;
  sid_before : sid;
}

type backend = {
  args : string list;
  file : string;
  top : Rocq_toplevel.toplevel;
  mutable top_refs : int;
  mutable rev_processed : in_toplevel list;
  mutable synced : t list;
}

and t = {
  mutable backend : backend option;
  mutable rev_prefix : processed list;
  mutable cursor_off : int;
  mutable suffix : unprocessed list;
}

let unsync : backend -> t -> unit = fun b d ->
  b.synced <- List.filter (fun s -> s != d) b.synced

let synced : backend -> t -> bool = fun b d ->
  List.memq d b.synced

let init : args:string list -> file:string -> t = fun ~args ~file ->
  let top = Rocq_toplevel.init ~args:(args @ ["-topfile"; file]) in
  let b = {args; file; top; top_refs = 1; rev_processed = []; synced = []} in
  let d = {backend = Some(b); rev_prefix = []; cursor_off = 0; suffix = []} in
  b.synced <- [d]; d

exception Stopped

let get_backend : t -> backend = fun d ->
  match d.backend with
  | Some(b) -> b
  | None    -> raise Stopped

let stop : t -> unit = fun d ->
  let backend = get_backend d in
  backend.top_refs <- backend.top_refs - 1;
  unsync backend d;
  if backend.top_refs = 0 then Rocq_toplevel.stop backend.top;
  d.backend <- None

let clone : t -> t = fun d ->
  let backend = get_backend d in
  backend.top_refs <- backend.top_refs + 1;
  let d_clone = {d with backend = d.backend} in
  if synced backend d then backend.synced <- d_clone :: backend.synced;
  d_clone

let file : t -> string = fun d ->
  if d.backend = None then raise Stopped;
  (get_backend d).file

let get_synced_backend : t -> backend = fun d ->
  let backend = get_backend d in
  (* match synced backend d with true -> backend | false -> *)
  backend.synced <- [d]; (* NOTE: we could avoid this in some cases. *)
  let rec common_prefix rev_processed rev_prefix processed prefix =
    match (processed, prefix) with
    (* Matching processed item, recursing. *)
    | (pr :: processed, p :: prefix) when pr.processed = p ->
        common_prefix (pr :: rev_processed) (p :: rev_prefix) processed prefix
    (* Different processed item (or no more expected items), rollback. *)
    | (pr :: _        , _          )                       ->
        (Some(pr.sid_before), rev_processed, prefix)
    (* In sync already. *)
    | ([]             , _          )                       ->
        (None, rev_processed, prefix)
  in
  let (rollback_sid, rev_processed, prefix) =
    let processed = List.rev backend.rev_processed in
    let prefix = List.rev d.rev_prefix in
    common_prefix [] [] processed prefix
  in
  (* Bringing the top-level to a common state. *)
  backend.rev_processed <- rev_processed;
  let sid =
    match rollback_sid with
    | None      -> Rocq_toplevel.StateID.current backend.top
    | Some(sid) ->
    match Rocq_toplevel.back_to backend.top ~sid with
    | Error(_) -> assert false
    | Ok(_)    -> sid
  in
  (* Replaying the remaining prefix commands. *)
  let replay sid_before processed =
    backend.rev_processed <- {processed; sid_before} :: backend.rev_processed;
    let run ~off ~text =
      match Rocq_toplevel.run backend.top ~off ~text with
      | Ok(_)      -> Rocq_toplevel.StateID.current backend.top
      | Error(_,_) -> assert false
    in
    match processed with
    | Blanks(_)               -> sid_before
    | Command({off; text; _}) -> run ~off ~text
    | Ghost({text; _})        -> run ~off:0 ~text
  in
  ignore (List.fold_left replay sid prefix); backend

let sync : t -> unit = fun d ->
  ignore (get_synced_backend d)

let is_synced : t -> bool = fun d ->
  synced (get_backend d) d

let cursor_index : t -> int = fun d ->
  if d.backend = None then raise Stopped;
  match d.rev_prefix with
  | []                       -> 0
  | Blanks({index; _})  :: _ -> index + 1
  | Command({index; _}) :: _ -> index + 1
  | Ghost({index; _})   :: _ -> index + 1

let to_unprocessed : Rocq_split_api.sentence -> unprocessed = fun s ->
  let text = s.Rocq_split_api.text in
  match s.Rocq_split_api.kind with
  | "blanks" -> RemBlanks({text})
  | _        -> RemCommand({text})

type loc = Rocq_loc.t option

let load_file : t -> (unit, string * loc) result = fun d ->
  let {file; args; _} = get_backend d in
  match Rocq_split_api.get ~args ~file with
  | Error(err)    -> Error(Rocq_split_api.(err.message, err.loc))
  | Ok(sentences) ->
  let suffix = List.rev_map to_unprocessed sentences in
  d.suffix <- List.rev_append suffix d.suffix;
  Ok(())

type command_data = Rocq_toplevel.run_data
type command_error = Rocq_toplevel.run_error

let insert_blanks : t -> text:string -> unit = fun d ~text ->
  let backend = get_synced_backend d in
  backend.synced <- [d];
  let len = String.length text in
  if len = 0 then () else
  match d.rev_prefix with
  | Blanks({index; off; text = blanks}) :: rev_prefix ->
      let processed = Blanks({index; off; text = blanks ^ text}) in
      let (sid_before, rev_processed) =
        match backend.rev_processed with
        | {sid_before; _} :: rev_commands -> (sid_before, rev_commands)
        | _                               -> assert false
      in
      backend.rev_processed <- {sid_before; processed} :: rev_processed;
      d.rev_prefix <- processed :: rev_prefix;
      d.cursor_off <- d.cursor_off + len
  | _                                                 ->
      let index = cursor_index d in
      let processed = Blanks({index; off = d.cursor_off; text}) in
      let sid_before = Rocq_toplevel.StateID.current backend.top in
      backend.rev_processed <-
        {sid_before; processed} :: backend.rev_processed;
      d.rev_prefix <- processed :: d.rev_prefix;
      d.cursor_off <- d.cursor_off + len

let insert_command : t -> text:string ->
    (command_data, string * command_error) result = fun d ~text ->
  let backend = get_synced_backend d in
  backend.synced <- [d];
  let off = d.cursor_off in
  let sid_before = Rocq_toplevel.StateID.current backend.top in
  let res = Rocq_toplevel.run backend.top ~off ~text in
  match res with Error(_,_) -> res | Ok(_) ->
  let processed = Command({index = cursor_index d; off; text}) in
  backend.rev_processed <- {sid_before; processed} :: backend.rev_processed;
  d.rev_prefix <- processed :: d.rev_prefix;
  d.cursor_off <- d.cursor_off + String.length text;
  res

let run_command : t -> text:string -> (command_data, string) result =
    fun d ~text ->
  let backend = get_synced_backend d in
  backend.synced <- [d];
  let sid_before = Rocq_toplevel.StateID.current backend.top in
  match Rocq_toplevel.run backend.top ~off:0 ~text with
  | Error(s,_) -> Error(s)
  | Ok(data)   ->
  let processed = Ghost({index = cursor_index d; off = d.cursor_off; text}) in
  backend.rev_processed <- {sid_before; processed} :: backend.rev_processed;
  d.rev_prefix <- processed :: d.rev_prefix;
  Ok(data)

let revert_before : ?erase:bool -> t -> index:int -> unit =
    fun ?(erase=false) d ~index:i ->
  let cur_index = cursor_index d in
  if i < 0 || cur_index < i then invalid_arg "index out of bounds";
  match i = cur_index with true -> () | false ->
  unsync (get_backend d) d;
  let rec revert rev_prefix suffix off =
    match rev_prefix with
    | []              -> assert (i = 0); (rev_prefix, suffix, off)
    | p :: rev_prefix ->
    let (index, off, item) =
      match p with
      | Blanks({index; text; off})  -> (index, off, RemBlanks({text}) )
      | Command({index; text; off}) -> (index, off, RemCommand({text}))
      | Ghost({index; text; off})   -> (index, off, RemGhost({text})  )
    in
    let suffix = item :: suffix in
    if index = i then
      (rev_prefix, suffix, off)
    else
      revert rev_prefix suffix off
  in
  let (rev_prefix, suffix, off) = revert d.rev_prefix d.suffix d.cursor_off in
  (* NOTE: no need to re-focus, the toplevel just gets out of sync. *)
  d.rev_prefix <- rev_prefix;
  d.cursor_off <- off ;
  (* TODO: this offset is not correct if the last command was inserted by [run_command] *)
  if not erase then d.suffix <- suffix

let with_rollback : t -> (unit -> 'a) -> 'a = fun d f ->
  let backend = get_synced_backend d in
  let rev_prefix = d.rev_prefix in
  let cursor_off = d.cursor_off in
  let suffix = d.suffix in
  let v = f () in
  d.rev_prefix <- rev_prefix;
  d.cursor_off <- cursor_off;
  d.suffix <- suffix;
  unsync backend d; v

let clear_suffix : t -> unit = fun d ->
  if d.backend = None then raise Stopped;
  d.suffix <- []

type byte_loc = {off : int; len : int}

let byte_loc_of_last_step : t -> byte_loc option = fun d ->
  if d.backend = None then raise Stopped;
  match d.rev_prefix with
  | []                           -> None
  | Blanks({off; text; _})  :: _
  | Command({off; text; _}) :: _ -> Some({off; len = String.length text})
  | Ghost(_)                :: _ -> None

let run_step : t ->
    (command_data option, string * command_error option) result = fun d ->
  if d.backend = None then raise Stopped;
  match d.suffix with
  | []                           -> Error("no step left to run", None)
  | RemBlanks({text})  :: suffix ->
      d.suffix <- suffix;
      insert_blanks d ~text; Ok(None)
  | RemCommand({text}) :: suffix ->
      begin
        match insert_command d ~text with
        | Ok(v)      -> d.suffix <- suffix; Ok(Some(v))
        | Error(s,d) -> Error(s, Some(d))
      end
  | RemGhost({text})   :: suffix ->
      begin
        match run_command d ~text with
        | Ok(v)    -> d.suffix <- suffix; Ok(Some(v))
        | Error(s) -> Error(s, None)
      end

let advance_to : t -> index:int -> (unit, string * command_error) result =
    fun d ~index ->
  let cur = cursor_index d in
  let len_suffix = List.length d.suffix in
  let one_past = cur + len_suffix in
  if index < cur || one_past < index then invalid_arg "index out of bounds";
  let rec loop cur =
    if cur = index then Ok(()) else
    match run_step d with
    | Ok(_) -> loop (cur + 1)
    | Error(s, Some(d)) -> Error(s, d)
    | Error(_, None) -> assert false (* Unreachable since correct index. *)
  in
  loop cur

let go_to : t -> index:int -> (unit, string * command_error) result =
    fun d ~index ->
  let cur = cursor_index d in
  match index < cur with
  | true  -> revert_before d ~index ~erase:false; Ok(())
  | false -> advance_to d ~index

type processed_item = {
  index : int;
  kind : [`Blanks | `Command | `Ghost];
  off : int;
  text : string;
}

let last_processed_item : t -> processed_item option = fun d ->
  if d.backend = None then raise Stopped;
  match d.rev_prefix with
  | Blanks({index; off; text})  :: _ ->
      Some({index; kind = `Blanks; off; text})
  | Command({index; off; text}) :: _ ->
      Some({index; kind = `Command; off; text})
  | Ghost({index; off; text})   :: _ ->
      Some({index; kind = `Ghost; off; text})
  | []                               ->
      None

type unprocessed_item = {
  kind : [`Blanks | `Command | `Ghost];
  text : string;
}

let first_unprocessed_item : t -> unprocessed_item option = fun d ->
  if d.backend = None then raise Stopped;
  match d.suffix with
  | []                      -> None
  | RemBlanks({text})  :: _ -> Some({kind = `Blanks ; text})
  | RemCommand({text}) :: _ -> Some({kind = `Command; text})
  | RemGhost({text})   :: _ -> Some({kind = `Ghost  ; text})

let doc_prefix : t -> (kind:string -> off:int -> text:string -> 'a)
     -> 'a list = fun d f ->
  if d.backend = None then raise Stopped;
  let rec build acc rev_prefix =
    match rev_prefix with
    | []                                    -> acc
    | Blanks({off; text; _})  :: rev_prefix ->
        build (f ~kind:"blanks" ~off ~text :: acc) rev_prefix
    | Command({off; text; _}) :: rev_prefix ->
        build (f ~kind:"command" ~off ~text :: acc) rev_prefix
    | Ghost({off; text; _})   :: rev_prefix ->
        build (f ~kind:"ghost" ~off ~text :: acc) rev_prefix
  in
  build [] d.rev_prefix

let doc_suffix : t -> (kind:string -> text:string -> 'a)
    -> 'a list = fun d f ->
  if d.backend = None then raise Stopped;
  let rec build suffix =
    match suffix with
    | []                           -> []
    | RemBlanks({text})  :: suffix ->
        f ~kind:"blanks"  ~text :: build suffix
    | RemCommand({text}) :: suffix ->
        f ~kind:"command" ~text :: build suffix
    | RemGhost({text})   :: suffix ->
        f ~kind:"ghost"   ~text :: build suffix
  in
  build d.suffix

let has_suffix : t -> bool = fun d ->
  if d.backend = None then raise Stopped;
  d.suffix <> []

let commit : t -> include_suffix:bool -> unit = fun d ~include_suffix ->
  let backend = get_backend d in
  Out_channel.with_open_text backend.file @@ fun oc ->
  let output_processed p =
    match p with
    | Blanks({text; _})  -> Out_channel.output_string oc text
    | Command({text; _}) -> Out_channel.output_string oc text
    | Ghost(_)           -> ()
  in
  List.iter output_processed (List.rev d.rev_prefix);
  let output_unprocessed u =
    match u with
    | RemBlanks({text})  -> Out_channel.output_string oc text
    | RemCommand({text}) -> Out_channel.output_string oc text
    | RemGhost(_)        -> ()
  in
  if include_suffix then List.iter output_unprocessed d.suffix

let compile : t -> (unit, string) result * string * string = fun d ->
  let {file; args; _} = get_backend d in
  let args = "c" :: args @ [file] in
  let stdout = file ^ ".stdout" in
  let stderr = file ^ ".stderr" in
  let cmd = Filename.quote_command "rocq" ~stdout ~stderr args in
  let ret =
    match Unix.system cmd with
    | Unix.WEXITED(0)   -> Ok(())
    | Unix.WEXITED(i)   -> Error(Format.sprintf "Exited with code %i." i)
    | Unix.WSIGNALED(i) -> Error(Format.sprintf "Killed with signal %i." i)
    | Unix.WSTOPPED(i)  -> Error(Format.sprintf "Stopped by signal %i." i)
  in
  let out = In_channel.with_open_text stdout In_channel.input_all in
  Sys.remove stdout;
  let err = In_channel.with_open_text stderr In_channel.input_all in
  Sys.remove stderr;
  (ret, out, err)

let query : t -> text:string -> (command_data, string) result = fun d ~text ->
  with_rollback d @@ fun _ -> run_command d ~text

let get_info_or_notice : command_data -> string list = fun data ->
  let filter Rocq_toplevel.{level; text; _} =
    match level with
    | Feedback.Info | Feedback.Notice -> Some(text)
    | _ -> None
  in
  List.filter_map filter data.Rocq_toplevel.feedback_messages

let query_text : ?index:int -> t -> text:string -> (string, string) result =
    fun ?index d ~text ->
  match query d ~text with Error(s) -> Error(s) | Ok(data) ->
  match (index, get_info_or_notice data) with
  | (None   , [s]) -> Ok(s)
  | (None   , [] ) -> Error("no \"info\" / \"notice\" feedback")
  | (None   , _  ) -> Error("too much \"info\" / \"notice\" feedback")
  | (Some(i), ls ) ->
  match List.nth_opt ls i with
  | None    -> Error("no \"info\" / \"notice\" feedback at the given index")
  | Some(s) -> Ok(s)

let query_text_all : ?indices:int list -> t -> text:string ->
    (string list, string) result = fun ?indices d ~text ->
  match query d ~text with Error(s) -> Error(s) | Ok(data) ->
  let feedback = get_info_or_notice data in
  match indices with
  | None          -> Ok(feedback)
  | Some(indices) ->
  let feedback = Array.of_list feedback in
  let rec build_res rev_items indices =
    match indices with
    | []               -> Ok(List.rev rev_items)
    | index :: indices ->
    try
      let item = Array.get feedback index in
      build_res (item :: rev_items) indices
    with Invalid_argument(_) ->
      Error("no \"info\" / \"notice\" feedback at one of the given indices")
  in
  build_res [] indices

type json = Yojson.Safe.t

let query_json : ?index:int -> t -> text:string -> (json, string) result =
    fun ?index d ~text ->
  match query_text ?index d ~text with Error(s) -> Error(s) | Ok(text) ->
  try Ok(Yojson.Safe.from_string text) with Yojson.Json_error(_) ->
  Error("the query result does not contain valid JSON")

let query_json_all : ?indices:int list -> t -> text:string ->
    (json list, string) result = fun ?indices d ~text ->
  match query_text_all ?indices d ~text with Error(s) -> Error(s) | Ok(l) ->
  try Ok(List.map Yojson.Safe.from_string l) with Yojson.Json_error(_) ->
  Error("Not all results of the query contain valid JSON")

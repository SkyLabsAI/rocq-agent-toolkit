type sid = Rocq_toplevel.StateID.t

type item_kind = [`Blanks | `Command | `Ghost]
[@@deriving to_yojson]

type processed_item = {
  index : int;
  kind : item_kind;
  off : int;
  text : string;
}
[@@deriving to_yojson]

type unprocessed_item = {
  kind : item_kind;
  text : string;
}
[@@deriving to_yojson]

type in_toplevel = {
  processed : processed_item;
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
  mutable rev_prefix : processed_item list;
  mutable cursor_off : int;
  mutable suffix : unprocessed_item list;
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

let materialize : t -> (unit, string) result = fun d ->
  let backend = get_backend d in
  match backend.top_refs with
  | 0 -> assert false
  | 1 -> Ok(())
  | _ ->
  match Rocq_toplevel.fork backend.top with
  | Error(s) -> Error(s)
  | Ok(top)  ->
  let new_backend =
    let synced = if synced backend d then [d] else [] in
    {backend with top; top_refs = 1; synced}
  in
  d.backend <- Some(new_backend);
  backend.top_refs <- backend.top_refs - 1;
  unsync backend d;
  Ok(())

let file : t -> string = fun d ->
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
    let run off text =
      match Rocq_toplevel.run backend.top ~off ~text with
      | Ok(_)      -> Rocq_toplevel.StateID.current backend.top
      | Error(_,_) -> assert false
    in
    match processed.kind with
    | `Blanks  -> sid_before
    | `Command -> run processed.off processed.text
    | `Ghost   -> run 0 processed.text
  in
  ignore (List.fold_left replay sid prefix); backend

let sync : t -> unit = fun d ->
  ignore (get_synced_backend d)

let is_synced : t -> bool = fun d ->
  synced (get_backend d) d

let copy_contents : from:t -> t -> unit = fun ~from d ->
  let backend = get_backend d in
  unsync backend d;
  d.suffix <- from.suffix;
  d.cursor_off <- from.cursor_off;
  d.rev_prefix <- from.rev_prefix

let cursor_index : t -> int = fun d ->
  ignore (get_backend d);
  match d.rev_prefix with [] -> 0 | p :: _ -> p.index + 1

let to_unprocessed : Rocq_split_api.sentence -> unprocessed_item = fun s ->
  let text = s.Rocq_split_api.text in
  match s.Rocq_split_api.kind with
  | "blanks" -> {kind = `Blanks ; text}
  | _        -> {kind = `Command; text}

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
  let backend = get_backend d in
  let processed =
    let index = cursor_index d in
    {index; kind = `Blanks; off = d.cursor_off; text}
  in
  d.rev_prefix <- processed :: d.rev_prefix;
  d.cursor_off <- d.cursor_off + String.length text;
  (* NOTE: only update the backend if we were in sync before inserting. *)
  if synced backend d then begin
    let sid_before = Rocq_toplevel.StateID.current backend.top in
    backend.rev_processed <- {sid_before; processed} :: backend.rev_processed;
    backend.synced <- [d]
  end

let insert_command : t -> text:string ->
    (command_data, string * command_error) result = fun d ~text ->
  let backend = get_synced_backend d in
  let off = d.cursor_off in
  let sid_before = Rocq_toplevel.StateID.current backend.top in
  let res = Rocq_toplevel.run backend.top ~off ~text in
  match res with Error(_,_) -> res | Ok(_) ->
  let processed = {index = cursor_index d; kind = `Command; off; text} in
  d.rev_prefix <- processed :: d.rev_prefix;
  d.cursor_off <- d.cursor_off + String.length text;
  backend.rev_processed <- {sid_before; processed} :: backend.rev_processed;
  backend.synced <- [d];
  res

let run_command : t -> text:string -> (command_data, string) result =
    fun d ~text ->
  let backend = get_synced_backend d in
  let sid_before = Rocq_toplevel.StateID.current backend.top in
  let res = Rocq_toplevel.run backend.top ~off:0 ~text in
  match res with Error(s,_) -> Error(s) | Ok(data) ->
  let off = d.cursor_off in
  let processed = {index = cursor_index d; kind = `Ghost; off; text} in
  d.rev_prefix <- processed :: d.rev_prefix;
  backend.rev_processed <- {sid_before; processed} :: backend.rev_processed;
  backend.synced <- [d];
  Ok(data)

let revert_before : ?erase:bool -> t -> index:int -> unit =
    fun ?(erase=false) d ~index:i ->
  let cur_index = cursor_index d in
  if i < 0 || cur_index < i then invalid_arg "index out of bounds";
  match i = cur_index with true -> () | false ->
  let rec revert (rev_prefix : processed_item list) suffix =
    match rev_prefix with
    | []              -> assert (i = 0); (rev_prefix, suffix, d.cursor_off)
    | p :: rev_prefix ->
    let suffix =
      match erase with
      | false -> {kind = p.kind; text = p.text} :: suffix
      | true  -> suffix
    in
    match p.index = i with
    | true  -> (rev_prefix, suffix, p.off)
    | false -> revert rev_prefix suffix
  in
  let (rev_prefix, suffix, off) = revert d.rev_prefix d.suffix in
  (* NOTE: no need to re-focus, the toplevel just gets out of sync. *)
  d.rev_prefix <- rev_prefix;
  d.cursor_off <- off;
  d.suffix <- suffix;
  unsync (get_backend d) d

let with_rollback : t -> (unit -> 'a) -> 'a = fun d f ->
  let backend = get_backend d in
  let rev_prefix = d.rev_prefix in
  let cursor_off = d.cursor_off in
  let suffix = d.suffix in
  let v = f () in
  d.rev_prefix <- rev_prefix;
  d.cursor_off <- cursor_off;
  d.suffix <- suffix;
  unsync backend d; v

let clear_suffix : ?count:int -> t -> unit = fun ?count d ->
  ignore (get_backend d);
  match count with
  | None        -> d.suffix <- []
  | Some(0)     -> ()
  | Some(count) ->
  if count < 0 then invalid_arg "negative count";
  if List.length d.suffix < count then invalid_arg "invalid count";
  d.suffix <- List.drop count d.suffix

let run_step : t ->
    (command_data option, string * command_error option) result = fun d ->
  ignore (get_backend d);
  match d.suffix with
  | []                                -> Error("no step left to run", None)
  | {kind = `Blanks ; text} :: suffix ->
      d.suffix <- suffix;
      insert_blanks d ~text; Ok(None)
  | {kind = `Command; text} :: suffix ->
      begin
        match insert_command d ~text with
        | Ok(v)      -> d.suffix <- suffix; Ok(Some(v))
        | Error(s,d) -> Error(s, Some(d))
      end
  | {kind = `Ghost  ; text} :: suffix ->
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

let rev_prefix : t -> processed_item list = fun d ->
  ignore (get_backend d); d.rev_prefix

let suffix : t -> unprocessed_item list = fun d ->
  ignore (get_backend d); d.suffix

let commit : ?file:string -> ?include_suffix:bool -> t -> unit =
    fun ?file ?(include_suffix=true) d ->
  let backend = get_backend d in
  let file = Stdlib.Option.value file ~default:backend.file in
  Out_channel.with_open_text file @@ fun oc ->
  let output_processed (p : processed_item) =
    match p.kind with
    | `Ghost -> ()
    | _      -> Out_channel.output_string oc p.text
  in
  List.iter output_processed (List.rev d.rev_prefix);
  let output_unprocessed u =
    match u.kind with
    | `Ghost -> ()
    | _      -> Out_channel.output_string oc u.text
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

type dump = {
  rev_processed : (int * processed_item) list option;
  rev_prefix : processed_item list;
  cursor_off : int;
  suffix : unprocessed_item list;
}
[@@deriving to_yojson]

let dump : t -> Yojson.Safe.t = fun d ->
  let {backend; rev_prefix; cursor_off; suffix} = d in
  let get_processed {top; rev_processed; _} =
    let explicit_sid {processed; sid_before} =
      (Rocq_toplevel.StateID.to_int top sid_before, processed)
    in
    List.map explicit_sid rev_processed
  in
  let rev_processed = Option.map get_processed backend in
  dump_to_yojson {rev_processed; rev_prefix; cursor_off; suffix}

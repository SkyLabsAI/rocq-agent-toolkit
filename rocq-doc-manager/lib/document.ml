type json = Yojson.Safe.t

type sid = Rocq_toplevel.StateID.t

type 'a processed =
  | Blanks of {index : int; off : int; text : string}
  | Command of {index : int; off : int; sid_before : 'a; text : string; visible:bool}

type unprocessed =
  | RemBlanks of {text : string}
  | RemCommand of {text : string}

type backend = {
  args : string list;
  file : string;
  toplevel : Rocq_toplevel.toplevel; (* TODO: this could be explicitly reference counted, or tracked using Gc.finalise *)
  (* initial_sid : sid; -- not necessary? *)
  mutable rev_commands : sid processed list;
  (* ^^ this does not need visible, but blanks are potentially still relevant
     since the offsets could be stored
   *)
  (* mutable cursor_sid : sid; -- not necessary? *)
  (* mutable cursor_off : int; -- not necessary? *)
}

type t = {
  backend : backend;
  initial_sid : sid;
  mutable rev_prefix : sid processed list;
  mutable cursor_sid : sid;
  mutable cursor_off : int;
  mutable suffix : unprocessed list;
}

let file : t -> string = fun d ->
  d.backend.file

let take_drop : type a. int -> a list -> a list * a list =
  (* [take_drop at ls = (rpre, post)] such that
    [length rpre = at && rev_append rpre post = ls] *)
  let rec go acc at ls =
    if at <= 0 then (acc, ls)
    else match ls with
        | [] -> (acc, ls)
        | l :: ls -> go (l :: acc) (at - 1) ls
  in fun at ls -> go [] at ls
;;

let%test "take_drop 0 []" = take_drop 0 [] = ([], [])
let%test "take_drop 0 [1]" = take_drop 0 [1] = ([], [1])
let%test "take_drop 1 [1]" = take_drop 1 [1] = ([1], [])
let%test "take_drop 1 [1;2]" = take_drop 1 [1;2] = ([1], [2])
let%test "take_drop 2 [1;2;3;4;5]" = take_drop 2 [1;2;3;4;5] = ([2;1], [3;4;5])

let revert_replay : type a. a processed list -> a processed list -> a option * a processed list =
  fun src dst ->
    let rec find_common : a processed list -> a processed list -> a option -> a processed list -> a option * a processed list =
      fun src dst cur_sid acc ->
        if src = dst then (cur_sid, acc)
        else match src , dst with
            | Blanks _ :: src , d :: dst -> find_common src dst cur_sid (d :: acc)
            | Command {sid_before; _} :: src, d :: dst -> find_common src dst (Some sid_before) (d :: acc)
            | [] , [] -> assert false (* src <> dst *)
            | [] , _ :: _
            | _ :: _ , [] -> assert false (* lists must be same length *)
    in
    if dst = src then (None, [])
    else
      let dst_len = List.length dst in
      let src_len = List.length src in
      if dst_len = src_len
      then find_common src dst None []
      else if src_len < dst_len then
        let replay , dst = take_drop (dst_len - src_len) dst in
        find_common src dst None replay
      else (* src_len > dst_len *)
        let rec drop_with_sid i sid = function
          | [] -> sid, []
          | ls when i <= 0 -> sid, ls
          | Blanks _ :: ls -> drop_with_sid (i-1) sid ls
          | Command {sid_before; _} :: ls -> drop_with_sid (i-1) (Some sid_before) ls
        in
        let sid, src = drop_with_sid (src_len - dst_len) None src in
        assert (List.length src = List.length dst);
        find_common src dst sid []
;;

let%test "[],[]" =
  revert_replay [] [] = (None, [])
let%test "[Blanks],[Blanks]" =
  let procs = [Blanks{index=0;off=0;text=""}] in
  revert_replay procs procs = (None, [])
let%test "[C1],[C1]" =
  let procs = [Command{index=0;off=0;sid_before=0;text="";visible=true}] in
  revert_replay procs procs = (None, [])
let%test "[],[C1]" =
  let src = [] in
  let dst = [Command{index=0;off=0;sid_before=3;text="bar.";visible=true}] in
  revert_replay src dst = (None, dst)
let%test "[C1],[]" =
  let src = [Command{index=0;off=0;sid_before=5;text="foo.";visible=true}] in
  let dst = [] in
  revert_replay src dst = (Some 5, [])
let%test "[C1],[C2]" =
  let src = [Command{index=0;off=0;sid_before=5;text="foo.";visible=true}] in
  let dst = [Command{index=0;off=0;sid_before=3;text="bar.";visible=true}] in
  revert_replay src dst = (Some 5, dst)
let%test "[C2;C1],[C1]" =
  let c1 = Command{index=0;off=0;sid_before=5;text="foo.";visible=true} in
  let c2 = Command{index=1;off=0;sid_before=3;text="bar.";visible=true} in
  (* NOTE: list is reversed *)
  revert_replay [c2;c1] [c1] = (Some 3, [])

(** returns the backend focused to the current cusor *)
let focused (cursor : t) : backend =
  let backend = cursor.backend in
  let revert , replay = revert_replay backend.rev_commands cursor.rev_prefix in
  let toplevel = backend.toplevel in
  let _ =
    match revert with
    | Some revert ->
      assert (Rocq_toplevel.back_to toplevel ~sid:revert = Ok ())
    | _ -> ()
  in
  let _ =
    List.iter (function
        | Blanks _ -> ()
        | Command {off;text;_} ->
          match Rocq_toplevel.run toplevel ~off ~text with
          | Ok _ -> ()
          | Error _ -> assert false
    ) replay
  in
  backend.rev_commands <- cursor.rev_prefix ;
  backend
;;

let focus_run : t -> off:int -> text:string -> _ * backend = fun d ~off ~text ->
  let backend = focused d in
  Rocq_toplevel.run backend.toplevel ~off ~text, backend

let cursor_index : t -> int = fun d ->
  match d.rev_prefix with
  | []                       -> 0
  | Blanks({index; _})  :: _ -> index + 1
  | Command({index; _}) :: _ -> index + 1

let init : args:string list -> file:string -> t = fun ~args ~file ->
  let toplevel = Rocq_toplevel.init ~args:(args @ ["-topfile"; file]) in
  let initial_sid = Rocq_toplevel.StateID.current toplevel in
  let cursor_sid = initial_sid in
  let cursor_off = 0 in
  let (rev_prefix, suffix) = ([], []) in
  let backend = { args; file; toplevel; rev_commands=rev_prefix } in
  { backend; initial_sid;
    rev_prefix; cursor_sid; cursor_off; suffix }

let stop : t -> unit = fun d ->
  Rocq_toplevel.stop d.backend.toplevel

let to_unprocessed : Rocq_split_api.sentence -> unprocessed = fun s ->
  let text = s.Rocq_split_api.text in
  match s.Rocq_split_api.kind with
  | "blanks" -> RemBlanks({text})
  | _        -> RemCommand({text})

type loc = Rocq_loc.t option

let load_file : t -> (unit, string * loc) result = fun d ->
  let {file; args; _} = d.backend in
  match Rocq_split_api.get ~args ~file with
  | Error(err)    -> Error(Rocq_split_api.(err.message, err.loc))
  | Ok(sentences) ->
  let suffix = List.rev_map to_unprocessed sentences in
  d.suffix <- List.rev_append suffix d.suffix;
  Ok(())

type command_data = Rocq_toplevel.run_data
type command_error = Rocq_toplevel.run_error

let insert_blanks : t -> text:string -> unit = fun d ~text ->
  let len = String.length text in
  if len = 0 then () else
  match d.rev_prefix with
  | Blanks({index; off; text = blanks}) :: rev_prefix ->
      let text = blanks ^ text in
      let elem = Blanks({index; off; text}) in
      d.backend.rev_commands <- elem :: d.backend.rev_commands ;
      d.rev_prefix <- elem :: rev_prefix;
      d.cursor_off <- d.cursor_off + len
  | _                                                 ->
      let index = cursor_index d in
      let off = d.cursor_off in
      d.backend.rev_commands <- Blanks({index; off; text}) :: d.backend.rev_commands;
      d.rev_prefix <- Blanks({index; off; text}) :: d.rev_prefix;
      d.cursor_off <- d.cursor_off + len

let insert_command : t -> text:string ->
    (command_data, string * command_error) result = fun d ~text ->
  let off = d.cursor_off in
  let sid_before = d.cursor_sid in
  let res, backend = focus_run d ~off ~text in
  match res with Error(_) -> res | _ ->
  let index = cursor_index d in
  let elem = Command({index; off; sid_before; text; visible=true}) in
  d.backend.rev_commands <- elem :: d.backend.rev_commands;
  d.rev_prefix <- elem :: d.rev_prefix;
  d.cursor_sid <- Rocq_toplevel.StateID.current backend.toplevel;
  d.cursor_off <- d.cursor_off + String.length text;
  res

let run_command : t -> text:string -> (command_data, string) result =
    fun d ~text ->
  match focus_run d ~off:0 ~text with
  | Error(s,_), _ -> Error(s)
  | Ok(data), backend   ->
    d.cursor_sid <- Rocq_toplevel.StateID.current backend.toplevel;
    Ok(data)

let revert_before : ?erase:bool -> t -> index:int -> unit =
    fun ?(erase=false) d ~index:i ->
  let cur_index = cursor_index d in
  if i < 0 || cur_index < i then invalid_arg "index out of bounds";
  if i = cur_index then () else
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
        assert (i = 0);
        (rev_prefix, suffix, d.initial_sid)
  in
  let (rev_prefix, suffix, sid) = revert d.rev_prefix d.suffix d.cursor_sid in
  (* NOTE: We don't actually need to re-focus the document because this returns a unit
  let _ = focused { d with rev_prefix; suffix; cursor_sid=sid } in
  *)
  d.rev_prefix <- rev_prefix;
  if not erase then d.suffix <- suffix;
  d.cursor_sid <- sid;
  () (* BUG: the offset is not updated! *)

let with_rollback : t -> (unit -> 'a) -> 'a = fun d f ->
  let rev_prefix = d.rev_prefix in
  let cursor_sid = d.cursor_sid in
  let cursor_off = d.cursor_off in
  let suffix = d.suffix in
  let v = f () in
  let _ = focused {d with rev_prefix; cursor_sid; cursor_off; suffix} in
  d.rev_prefix <- rev_prefix;
  d.cursor_sid <- cursor_sid;
  d.cursor_off <- cursor_off;
  d.suffix <- suffix; v

let clear_suffix : t -> unit = fun d ->
  d.suffix <- []

type byte_loc = {off : int; len : int}

let byte_loc_of_last_step : t -> byte_loc option = fun d ->
  match d.rev_prefix with [] -> None
  | Blanks({off; text; _})  :: _
  | Command({off; text; _}) :: _ ->
      Some({off; len = String.length text})

let run_step : t -> (command_data option, string * command_error option) result = fun d ->
  match d.suffix with
  | []             -> Error("no step left to run", None)
  | step :: suffix ->
  match step with
  | RemBlanks({text})  ->
    d.suffix <- suffix;
    insert_blanks d ~text; Ok(None)
  | RemCommand({text}) ->
  match insert_command d ~text with
  | Ok(v) ->
    d.suffix <- suffix;
    Ok(Some(v))
  | Error(s,d) -> Error(s, Some(d))

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

let go_to : t -> index:int -> (unit, string * command_error) result = fun d ~index ->
  let cur = cursor_index d in
  match index < cur with
  | true  -> revert_before d ~index ~erase:false; Ok(())
  | false -> advance_to d ~index

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

type unprocessed_item = {
  kind : [`Blanks | `Command];
  text : string;
}

let first_unprocessed_item : t -> unprocessed_item option = fun d ->
  match d.suffix with
  | []                      -> None
  | RemBlanks({text})  :: _ -> Some({kind = `Blanks; text})
  | RemCommand({text}) :: _ -> Some({kind = `Command; text})

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
  Out_channel.with_open_text d.backend.file @@ fun oc ->
  let output_processed p =
    match p with
    | Blanks({text; _}) -> Out_channel.output_string oc text
    | Command({text; visible;_}) ->
      if visible then Out_channel.output_string oc text
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
  let {file;args;_} = d.backend in
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
  let out = read_file stdout in
  Sys.remove stdout;
  let err = read_file stderr in
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

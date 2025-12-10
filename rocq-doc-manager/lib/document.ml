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
  toplevel : Rocq_toplevel.toplevel;
  mutable toplevel_refs : int;
  mutable rev_commands : sid processed list;
}

type t = {
  mutable backend : backend option;
  mutable rev_prefix : unit processed list;
  mutable cursor_off : int;
  mutable suffix : unprocessed list;
}

let init : args:string list -> file:string -> t = fun ~args ~file ->
  let toplevel = Rocq_toplevel.init ~args:(args @ ["-topfile"; file]) in
  let b = {args; file; toplevel; toplevel_refs = 0; rev_commands = []} in
  {backend = Some(b); rev_prefix = []; cursor_off = 0; suffix = []}

exception Stopped

let get_backend : t -> backend = fun d ->
  match d.backend with
  | Some(b) -> b
  | None    -> raise Stopped

let stop : t -> unit = fun d ->
  let backend = get_backend d in
  backend.toplevel_refs <- backend.toplevel_refs - 1;
  if backend.toplevel_refs = 0 then Rocq_toplevel.stop backend.toplevel;
  d.backend <- None

let clone : t -> t = fun d ->
  let backend = get_backend d in
  backend.toplevel_refs <- backend.toplevel_refs + 1;
  {d with backend = d.backend}

let file : t -> string = fun d ->
  if d.backend = None then raise Stopped;
  (get_backend d).file

let take_drop : type a. int -> a list -> a list * a list =
  (* [take_drop at ls = (rpre, post)] such that
    [length rpre = at && rev_append rpre post = ls] *)
  let rec go acc at ls =
    if at <= 0 then (acc, ls)
    else match ls with
        | [] -> (acc, ls)
        | l :: ls -> go (l :: acc) (at - 1) ls
  in fun at ls -> go [] at ls

let%test "take_drop 0 []" = take_drop 0 [] = ([], [])
let%test "take_drop 0 [1]" = take_drop 0 [1] = ([], [1])
let%test "take_drop 1 [1]" = take_drop 1 [1] = ([1], [])
let%test "take_drop 1 [1;2]" = take_drop 1 [1;2] = ([1], [2])
let%test "take_drop 2 [1;2;3;4;5]" = take_drop 2 [1;2;3;4;5] = ([2;1], [3;4;5])

let revert_replay : type a b. a processed list -> b processed list -> a option * a processed list * b processed list =
  let rec consistent : a processed list -> b processed list -> bool = fun ls rs ->
    match ls, rs with
    | [] , [] -> true
    | Blanks l :: ls , Blanks r :: rs ->
      if l.index = r.index && l.off = r.off && l.text = r.text then consistent ls rs else false
    | Command l :: ls , Command r :: rs ->
      if l.index = r.index && l.off = r.off && l.text = r.text then consistent ls rs else false
    | _ , _ -> false
  in
  fun src dst ->
    let rec find_common : a processed list -> b processed list -> a option -> b processed list -> a option * a processed list * b processed list =
      fun src dst cur_sid acc ->
        if consistent src dst then (cur_sid, src, acc)
        else match src , dst with
            | Blanks _ :: src , d :: dst -> find_common src dst cur_sid (d :: acc)
            | Command {sid_before; _} :: src, d :: dst -> find_common src dst (Some sid_before) (d :: acc)
            | [] , [] -> assert false (* src <> dst *)
            | [] , _ :: _
            | _ :: _ , [] -> assert false (* lists must be same length *)
    in
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

let%test "[],[]" =
  revert_replay [] [] = (None, [], [])
let%test "[Blanks],[Blanks]" =
  let procs = [Blanks{index=0;off=0;text=""}] in
  revert_replay procs procs = (None, procs, [])
let%test "[C1],[C1]" =
  let procs = [Command{index=0;off=0;sid_before=0;text="";visible=true}] in
  revert_replay procs procs = (None, procs, [])
let%test "[],[C1]" =
  let src = [] in
  let dst = [Command{index=0;off=0;sid_before=3;text="bar.";visible=true}] in
  revert_replay src dst = (None, src, dst)
let%test "[C1],[]" =
  let src = [Command{index=0;off=0;sid_before=5;text="foo.";visible=true}] in
  let dst = [] in
  revert_replay src dst = (Some 5, [], [])
let%test "[C1],[C2]" =
  let src = [Command{index=0;off=0;sid_before=5;text="foo.";visible=true}] in
  let dst = [Command{index=0;off=0;sid_before=3;text="bar.";visible=true}] in
  revert_replay src dst = (Some 5, [], dst)
let%test "[C2;C1],[C1]" =
  let c1 = Command{index=0;off=0;sid_before=5;text="foo.";visible=true} in
  let c2 = Command{index=1;off=0;sid_before=3;text="bar.";visible=true} in
  (* NOTE: list is reversed *)
  revert_replay [c2;c1] [c1] = (Some 3, [c1], [])

(*
let rec print_processed top out = function
  | [] -> output_string out "[]"
| Blanks _ :: ls -> output_string out "<blanks>::" ; print_processed top out ls
| Command {sid_before;_} :: ls ->
  output_string out (string_of_int @@ Rocq_toplevel.StateID.to_int top sid_before) ;
  output_string out "::" ;
  print_processed top out ls
*)

(** returns the backend focused to the current cusor *)
let focused (cursor : t) : backend =
  let backend = get_backend cursor in
  let revert , reverted_to , replay = revert_replay backend.rev_commands cursor.rev_prefix in
  let toplevel = backend.toplevel in
  let sid =
    match revert with
    | Some revert ->
      assert (Rocq_toplevel.back_to toplevel ~sid:revert = Ok ());
      revert
    | _ ->
      Rocq_toplevel.StateID.current toplevel
  in
  backend.rev_commands <- reverted_to ;
  let _ =
    List.fold_left (fun sid -> function
        | Blanks _ -> sid
        | Command {off;text;visible;index;_} ->
          match Rocq_toplevel.run toplevel ~off ~text with
          | Ok _ ->
            backend.rev_commands <- Command {off;text;visible;index;sid_before=sid} :: backend.rev_commands ;
            Rocq_toplevel.StateID.current toplevel
          | Error _ -> assert false
    ) sid replay
  in
  backend

let focus_run : t -> off:int -> text:string -> visible:bool -> _ result * backend =
  fun d ~off ~text ~visible ->
    let backend = focused d in
    let sid_before = Rocq_toplevel.StateID.current backend.toplevel in
    let res = Rocq_toplevel.run backend.toplevel ~off ~text in
    let _ =
      match res with
      | Ok _ ->
        backend.rev_commands <- Command {index=0;off;sid_before;text;visible} :: backend.rev_commands
      | Error _ -> ()
    in res, backend

let cursor_index : t -> int = fun d ->
  if d.backend = None then raise Stopped;
  match d.rev_prefix with
  | []                       -> 0
  | Blanks({index; _})  :: _ -> index + 1
  | Command({index; _}) :: _ -> index + 1

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
  let backend = get_backend d in
  let len = String.length text in
  if len = 0 then () else
  match d.rev_prefix with
  | Blanks({index; off; text = blanks}) :: rev_prefix ->
      let text = blanks ^ text in
      let elem = Blanks({index; off; text}) in
      backend.rev_commands <- elem :: backend.rev_commands ;
      d.rev_prefix <- elem :: rev_prefix;
      d.cursor_off <- d.cursor_off + len
  | _                                                 ->
      let index = cursor_index d in
      let off = d.cursor_off in
      backend.rev_commands <- Blanks({index; off; text}) :: backend.rev_commands;
      d.rev_prefix <- Blanks({index; off; text}) :: d.rev_prefix;
      d.cursor_off <- d.cursor_off + len

let insert_command : t -> text:string ->
    (command_data, string * command_error) result = fun d ~text ->
  let backend = focused d in
  let off = d.cursor_off in
  let sid_before = Rocq_toplevel.StateID.current backend.toplevel in
  let res = Rocq_toplevel.run backend.toplevel ~off ~text in
  match res with
  | Error _ as res -> res
  | _ ->
    let index = cursor_index d in
    let elem sid_before = Command({index; off; sid_before; text; visible=true}) in
    backend.rev_commands <- elem sid_before :: backend.rev_commands;
    d.rev_prefix <- elem () :: d.rev_prefix;
    d.cursor_off <- d.cursor_off + String.length text;
    res

let run_command : t -> text:string -> (command_data, string) result =
    fun d ~text ->
  match fst (focus_run d ~off:0 ~text ~visible:false) with
  | Error(s,_) -> Error(s)
  | Ok(data)   ->
      d.rev_prefix <- Command{off=0;index=1+List.length d.rev_prefix;sid_before=();text;visible=false}::d.rev_prefix;
      Ok(data)

let revert_before : ?erase:bool -> t -> index:int -> unit =
    fun ?(erase=false) d ~index:i ->
  let cur_index = cursor_index d in
  if i < 0 || cur_index < i then invalid_arg "index out of bounds";
  if i = cur_index then () else
  let rec revert rev_prefix suffix off =
    match rev_prefix with
    | Blanks({index; text; off})              :: rev_prefix ->
      let suffix = if not erase then RemBlanks({text}) :: suffix else suffix in
      if index = i then
        (rev_prefix, suffix, off)
      else
        revert rev_prefix suffix off
    | Command({index; text; off; visible;_}) :: rev_prefix ->
      let suffix = if not erase && visible then RemCommand({text}) :: suffix else suffix in
      if index = i then
        (rev_prefix, suffix, off)
      else
        revert rev_prefix suffix off
    | []                                                  ->
      assert (i = 0);
      (rev_prefix, suffix, off)
  in
  let (rev_prefix, suffix, off) = revert d.rev_prefix d.suffix d.cursor_off in
  (* NOTE: We don't actually need to re-focus the document because this returns a unit
  let _ = focused { d with rev_prefix; suffix; cursor_sid=sid } in
  *)
  d.rev_prefix <- rev_prefix;
  d.cursor_off <- off ;
  (* TODO: this offset is not correct if the last command was inserted by [run_command] *)
  if not erase then d.suffix <- suffix

let with_rollback : t -> (unit -> 'a) -> 'a = fun d f ->
  let _ = focused d in
  let rev_prefix = d.rev_prefix in
  let cursor_off = d.cursor_off in
  let suffix = d.suffix in
  let v = f () in
  d.rev_prefix <- rev_prefix;
  d.cursor_off <- cursor_off;
  d.suffix <- suffix; v

let clear_suffix : t -> unit = fun d ->
  if d.backend = None then raise Stopped;
  d.suffix <- []

type byte_loc = {off : int; len : int}

let byte_loc_of_last_step : t -> byte_loc option = fun d ->
  if d.backend = None then raise Stopped;
  match d.rev_prefix with [] -> None
  | Blanks({off; text; _})  :: _
  | Command({off; text; _}) :: _ ->
      Some({off; len = String.length text})

let run_step : t ->
    (command_data option, string * command_error option) result = fun d ->
  if d.backend = None then raise Stopped;
  match d.suffix with
  | []                           -> Error("no step left to run", None)
  | RemBlanks({text})  :: suffix ->
      d.suffix <- suffix;
      insert_blanks d ~text; Ok(None)
  | RemCommand({text}) :: suffix ->
      match insert_command d ~text with
      | Ok(v)      -> d.suffix <- suffix; Ok(Some(v))
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

let go_to : t -> index:int -> (unit, string * command_error) result =
    fun d ~index ->
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
  if d.backend = None then raise Stopped;
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
  if d.backend = None then raise Stopped;
  match d.suffix with
  | []                      -> None
  | RemBlanks({text})  :: _ -> Some({kind = `Blanks; text})
  | RemCommand({text}) :: _ -> Some({kind = `Command; text})

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
  let {file;args;_} = get_backend d in
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

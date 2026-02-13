(** Formatter with continuation. *)
type ('a, 'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

(** [panic fmt ...] interrupts the program with [exit 1], after displaying the
    error message specified by [fmt] (and subsequent arguments) to [stderr]. A
    newline character is added to the message, and [stderr] is flushed. *)
let panic : ('a,'b) koutfmt -> 'a = fun fmt ->
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter (fmt ^^ "\n%!")

module API = Jsonrpc_tp.API
module A = API.Args
module S = API.Schema

module IntMap = Map.Make(Int)

(** A cursor is a document handle, that cannot be worked on by several threads
    at the same time. A maximum of one request can run on any given cursor, at
    any given time. *)
module Cursor = struct
  type t = {
    doc : Document.t;
    (** Underlying document handle. *)
    active : bool Atomic.t;
    (** Boolean indicating whether the cursor is currently in use. *)
  }

  let make : Document.t -> t = fun doc ->
    {doc; active = Atomic.make false}

  let lock : t -> unit = fun c ->
    match Atomic.compare_and_set c.active false true with
    | true  -> ()
    | false ->
    match Document.is_stopped c.doc with
    | true  -> invalid_arg "cursor already stopped"
    | false -> invalid_arg "cursor already in use"

  let unlock : t -> unit = fun c ->
    Atomic.set c.active false
end

(** State of the API. *)
module State : sig
  type t

  val create : Document.t -> t

  val get_cursor : t -> int -> Cursor.t

  val insert_cursor : t -> Cursor.t -> int
end = struct
  (** State of the API, holding a map of active cursors. *)
  type t = {
    mutex : Mutex.t;
    mutable cursors: Cursor.t IntMap.t;
    mutable fresh: int
  }

  let create : Document.t -> t = fun doc ->
    let cursors = IntMap.singleton 0 (Cursor.make doc) in
    {mutex = Mutex.create (); fresh = 1; cursors}

  let get_cursor : t -> int -> Cursor.t = fun s k ->
    let get () = IntMap.find_opt k s.cursors in
    match Mutex.protect s.mutex get with
    | None         -> invalid_arg "unknown cursor"
    | Some(cursor) -> cursor

  let insert_cursor : t -> Cursor.t -> int = fun s cursor ->
    let new_key = ref 0 in
    let insert () =
      let k = s.fresh in
      s.fresh <- k + 1;
      new_key := k;
      s.cursors <- IntMap.add k cursor s.cursors
    in
    Mutex.protect s.mutex insert; !new_key
end

let api : State.t API.api = API.create ~name:"RocqDocManagerAPI"

module WithCursor : sig
  val declare_full : name:string ->
    ?descr:string ->
    args:'a A.t ->
    ret:'b S.t ->
    ?ret_descr:string ->
    err:'c S.t ->
    ?err_descr:string ->
    ?recoverable:bool ->
    (Document.t -> 'a -> ('b, string * 'c) result) ->
    unit

  val declare :
    name:string ->
    ?descr:string ->
    args:'a A.t ->
    ret:'b S.t ->
    ?ret_descr:string ->
    (Document.t -> 'a -> 'b) ->
    unit
end = struct
  let add_cursor_arg rest =
    let descr = "the cursor to perform the operation on" in
    A.add ~name:"cursor" ~descr S.int rest

  let at_cursor action _ toplevel (cursor, args) =
    let d = State.get_cursor toplevel cursor in
    Cursor.lock d;
    try
      let res = action d.doc args in
      Cursor.unlock d; res
    with Invalid_argument(_) as e ->
      Cursor.unlock d; raise e

  let declare_full ~name ?descr ~args ~ret ?ret_descr ~err ?err_descr
      ?recoverable action =
    let args = add_cursor_arg args in
    API.declare_full api ~name ?descr ~args ~ret ?ret_descr ~err ?err_descr
      ?recoverable (at_cursor action)

  let declare ~name ?descr ~args ~ret ?ret_descr action =
    let args = add_cursor_arg args in
    API.declare api ~name ?descr ~args ~ret ?ret_descr (at_cursor action)
end

open WithCursor

let rocq_loc =
  let rocq_source =
    let fields =
      API.Fields.add ~name:"dirpath" S.(nullable string) @@
      API.Fields.add ~name:"file" S.string @@
      API.Fields.nil
    in
    API.declare_object api ~name:"RocqSource"
      ~descr:"Rocq source file information"
      ~encode:Fun.id ~decode:Fun.id fields
  in
  let fields =
    API.Fields.add ~name:"fname"
      ~descr:"source file identification if not run as a toplevel"
      S.(nullable (obj rocq_source)) @@
    API.Fields.add ~name:"line_nb" ~descr:"start line number" S.int @@
    API.Fields.add ~name:"bol_pos"
      ~descr:"position of the beginning of start line" S.int @@
    API.Fields.add ~name:"line_nb_last" ~descr:"end line number" S.int @@
    API.Fields.add ~name:"bol_pos_last"
      ~descr:"position of the beginning of end line" S.int @@
    API.Fields.add ~name:"bp" ~descr:"start position" S.int @@
    API.Fields.add ~name:"ep" ~descr:"end position" S.int @@
    API.Fields.nil
  in
  let encode arg =
    let (fname, (line_nb, (bol_pos, arg))) = arg in
    let (line_nb_last, (bol_pos_last, (bp, (ep, ())))) = arg in
    let fname =
      match fname with
      | None                        -> Rocq_loc.ToplevelInput
      | Some((dirpath, (file, ()))) -> Rocq_loc.InFile({dirpath; file})
    in
    Rocq_loc.{fname; line_nb; bol_pos; line_nb_last; bol_pos_last; bp; ep}
  in
  let decode loc =
    let Rocq_loc.{fname; line_nb; bol_pos; _} = loc in
    let Rocq_loc.{line_nb_last; bol_pos_last; bp; ep; _} = loc in
    let fname =
      match fname with
      | Rocq_loc.ToplevelInput           -> None
      | Rocq_loc.InFile({dirpath; file}) -> Some((dirpath, (file, ())))
    in
    let ret = (line_nb_last, (bol_pos_last, (bp, (ep, ())))) in
    (fname, (line_nb, (bol_pos, ret)))
  in
  API.declare_object api ~name:"RocqLoc"
    ~descr:"Rocq source code location" ~encode ~decode fields

let _ =
  declare_full ~name:"load_file" ~descr:"adds the (unprocessed) \
      file contents to the document (note that this requires running \
      sentence-splitting, which requires the input file not to have syntax \
      errors)" ~args:A.nil ~ret:S.null ~err:S.(nullable (obj rocq_loc))
    ~err_descr:"optional source code location for the error"
    @@ fun d () ->
  Document.load_file d

let _ =
  let args =
    A.add ~name:"text" ~descr:"text of the blanks to insert" S.string @@
    A.nil
  in
  declare ~name:"insert_blanks"
    ~descr:"insert and process blanks at the cursor" ~args ~ret:S.null
    @@ fun d (text, ()) ->
  Document.insert_blanks d ~text

let quickfix =
  let fields =
    API.Fields.add ~name:"loc" S.(obj rocq_loc) @@
    API.Fields.add ~name:"text" S.string @@
    API.Fields.nil
  in
  let open Rocq_toplevel in
  let encode (loc, (text, ())) = {loc; text} in
  let decode ({loc; text} : quickfix) = (loc, (text, ())) in
  API.declare_object api ~name:"Quickfix"
    ~descr:"Quick fix hint" ~encode ~decode fields

let feedback_message =
  let level =
    let encode v =
      match v with
      | Feedback.Debug   -> "debug"
      | Feedback.Info    -> "info"
      | Feedback.Notice  -> "notice"
      | Feedback.Warning -> "warning"
      | Feedback.Error   -> "error"
    in
    S.variant ~encode Feedback.[Debug; Info; Notice; Warning; Error]
  in
  let fields =
    API.Fields.add ~name:"level" level @@
    API.Fields.add ~name:"loc" S.(nullable (obj rocq_loc)) @@
    API.Fields.add ~name:"quickfix" S.(list (obj quickfix)) @@
    API.Fields.add ~name:"text" S.string @@
    API.Fields.nil
  in
  let open Rocq_toplevel in
  let encode _ = assert false in
  let decode {level; loc; quickfix; text} =
    (level, (loc, (quickfix, (text, ()))))
  in
  API.declare_object api ~name:"FeedbackMessage"
    ~descr:"Rocq feedback message" ~encode ~decode fields

let globrefs_diff =
  let fields =
    API.Fields.add ~name:"added_constants" S.(list string) @@
    API.Fields.add ~name:"removed_constants" S.(list string) @@
    API.Fields.add ~name:"added_inductives" S.(list string) @@
    API.Fields.add ~name:"removed_inductives" S.(list string) @@
    API.Fields.nil
  in
  let open Rocq_toplevel in
  let encode _ = assert false in
  let decode diff =
    let {added_constants = ac; removed_constants = rc; _} = diff in
    let {added_inductives = ai; removed_inductives = ri; _} = diff in
    let ac = List.map Names.Constant.to_string ac in
    let rc = List.map Names.Constant.to_string rc in
    let ai = List.map Names.MutInd.to_string ai in
    let ri = List.map Names.MutInd.to_string ri in
    (ac, (rc, (ai, (ri, ()))))
  in
  let default =
    {added_constants = []; removed_constants = [];
     added_inductives = []; removed_inductives = []}
  in
  API.declare_object api ~name:"GlobrefsDiff" ~descr:"environment \
    modification performed by a Rocq command" ~default ~encode ~decode fields

let proof_state =
  let fields =
    API.Fields.add ~name:"given_up_goals" S.int @@
    API.Fields.add ~name:"shelved_goals" S.int @@
    API.Fields.add ~name:"unfocused_goals" S.(list int) @@
    API.Fields.add ~name:"focused_goals" S.(list string) @@
    API.Fields.nil
  in
  let open Rocq_toplevel in
  let encode arg =
    let (given_up_goals, (shelved_goals, arg)) = arg in
    let (unfocused_goals, (focused_goals, ())) = arg in
    {given_up_goals; shelved_goals; unfocused_goals; focused_goals}
  in
  let decode {given_up_goals; shelved_goals; unfocused_goals; focused_goals} =
    (given_up_goals, (shelved_goals, (unfocused_goals, (focused_goals, ()))))
  in
  API.declare_object api ~name:"ProofState" ~descr:"Summary of a Rocq proof \
    state, including the text of focused goals" ~encode ~decode fields

let command_data =
  let fields =
    API.Fields.add ~name:"globrefs_diff" S.(obj globrefs_diff) @@
    API.Fields.add ~name:"feedback_messages"
      S.(list (obj feedback_message)) @@
    API.Fields.add ~name:"proof_state" S.(nullable (obj proof_state)) @@
    API.Fields.nil
  in
  let open Rocq_toplevel in
  let encode (globrefs_diff, (feedback_messages, (proof_state, ()))) =
    {globrefs_diff; feedback_messages; proof_state}
  in
  let decode {globrefs_diff; feedback_messages; proof_state} =
    (globrefs_diff, (feedback_messages, (proof_state, ())))
  in
  API.declare_object api ~name:"CommandData"
    ~descr:"data gathered while running a Rocq command" ~encode ~decode fields

let command_error =
  let fields =
    API.Fields.add ~name:"error_loc" ~descr:"optional source code location \
      for the error" S.(nullable (obj rocq_loc)) @@
    API.Fields.add ~name:"feedback_messages"
      S.(list (obj feedback_message)) @@
    API.Fields.nil
  in
  let open Rocq_toplevel in
  let encode (error_loc, (feedback_messages, ())) =
    {error_loc; feedback_messages}
  in
  let decode {error_loc; feedback_messages} =
    (error_loc, (feedback_messages, ()))
  in
  API.declare_object api ~name:"CommandError"
    ~descr:"data returned on Rocq command errors" ~encode ~decode fields

let steps_error =
  let fields =
    API.Fields.add ~name:"nb_processed" ~descr:"number of unprocessed items \
      that were processed successfully" S.int @@
    API.Fields.add ~name:"cmd_error" S.(obj command_error) @@
    API.Fields.nil
  in
  let encode (nb_processed, (cmd_error, ())) = (nb_processed, cmd_error) in
  let decode (nb_processed, cmd_error) = (nb_processed, (cmd_error, ())) in
  API.declare_object api ~name:"StepsError"
    ~descr:"data returned by `run_steps`" ~encode ~decode fields

let text_args =
  A.add ~name:"text" ~descr:"text of the command to insert" S.string A.nil

let _ =
  declare_full ~name:"insert_command"
    ~descr:"insert and process a command at the cursor"
    ~args:text_args ~ret:S.(obj command_data)
    ~err:S.(obj command_error)
    ~err_descr:"optional source code location for the error"
    @@ fun d (text, ()) ->
  Document.insert_command d ~text

let _ =
  declare_full ~name:"run_command"
    ~descr:"process a command at the cursor without inserting it in the \
      document" ~args:text_args ~ret:S.(obj command_data) ~err:S.null
    @@ fun d (text, ()) ->
  let res = Document.insert_command ~ghost:true d ~text in
  Result.map_error (fun (s, _) -> (s, ())) res

let _ =
  declare ~name:"cursor_index"
    ~descr:"gives the index at the cursor"
    ~args:A.nil ~ret:S.int @@ fun d () ->
  Document.cursor_index d

let _ =
  let args =
    A.add ~name:"erase" ~descr:"boolean indicating whether reverted items \
      should be erased" S.bool @@
    A.add ~name:"index" ~descr:"index of the item before which the cursor \
      should be revered (one-past-the-end index allowed)" S.int @@
    A.nil
  in
  declare ~name:"revert_before" ~descr:"revert the cursor to an \
    earlier point in the document" ~args ~ret:S.null
    @@ fun d (erase, (index, ())) ->
  Document.revert_before d ~erase ~index

let index_before_args =
  A.add ~name:"index" ~descr:"integer index before which to move the cursor \
    (one-past-the-end index allowed)" S.int A.nil

let _ =
  declare_full ~name:"advance_to" ~descr:"advance the cursor \
    before the indicated unprocessed item" ~args:index_before_args ~ret:S.null
    ~err:S.(nullable (obj command_error))
    ~err_descr:"optional source code location for the error"
    @@ fun d (index, ()) ->
  Result.map_error (fun (e,v) -> e, Some v) @@ Document.advance_to d ~index

let _ =
  declare_full ~name:"go_to" ~descr:"move the cursor right before \
    the indicated item (whether it is already processed or not)"
    ~args:index_before_args ~ret:S.null ~err:S.(nullable (obj command_error))
    ~err_descr:"optional source code location for the error"
    @@ fun d (index, ()) ->
  Result.map_error (fun (e,v) -> e, Some v) @@ Document.go_to d ~index

let _ =
  let args =
    A.add ~name:"count" ~descr:"the number of unprocessed commands to \
      remove, or `null` to remove them all" S.(nullable int) @@
    A.nil
  in
  declare ~name:"clear_suffix" ~descr:"remove unprocessed commands from the \
    document" ~args ~ret:S.null @@ fun d (count, ()) ->
  Document.clear_suffix ?count d

let _ =
  declare_full ~name:"run_step" ~descr:"advance the cursor by \
      stepping over an unprocessed item" ~args:A.nil
    ~ret:S.(nullable (obj command_data))
    ~ret_descr:"data for the command that was run, if any"
    ~err:S.(obj command_error)
    ~err_descr:"error data for the command that was run"
    @@ fun d () ->
  Document.run_step d

let _ =
  let args =
    A.add ~name:"count" ~descr:"the number of unprocessed items to process"
      S.int @@
    A.nil
  in
  declare_full ~name:"run_steps" ~descr:"advance the cursor by stepping over \
      the given number of unprocessed item" ~args ~ret:S.null
    ~err:S.(obj steps_error)
    ~err_descr:"error data for the command that was run"
    @@ fun d (count, ()) ->
  let res = Document.run_steps d ~count in
  Result.map_error (fun (i, (s, e)) -> (s, (i, e))) res

let item_kind =
  let encode v =
    match v with
    | `Blanks  -> "blanks"
    | `Command -> "command"
    | `Ghost   -> "ghost"
  in
  S.variant ~encode [`Blanks; `Command; `Ghost]

let prefix_item =
  let fields =
    API.Fields.add ~name:"kind" item_kind @@
    API.Fields.add ~name:"offset" S.int @@
    API.Fields.add ~name:"text" S.string @@
    API.Fields.nil
  in
  API.declare_object api ~name:"PrefixItem"
    ~descr:"document prefix item, appearing before the cursor"
    ~encode:Fun.id ~decode:Fun.id fields

let _ =
  declare ~name:"doc_prefix" ~descr:"gives the list of all \
      processed commands, appearing before the cursor" ~args:A.nil
    ~ret:S.(list (obj prefix_item)) @@ fun d () ->
  let make (p : Document.processed_item) = (p.kind, (p.off, (p.text, ()))) in
  List.rev_map make (Document.rev_prefix d)

let suffix_item =
  let fields =
    API.Fields.add ~name:"kind" item_kind @@
    API.Fields.add ~name:"text" S.string @@
    API.Fields.nil
  in
  API.declare_object api ~name:"SuffixItem"
    ~descr:"document suffix item, appearing after the cursor"
    ~encode:Fun.id ~decode:Fun.id fields

let _ =
  declare ~name:"doc_suffix" ~descr:"gives the list of all \
      unprocessed commands, appearing after the cursor" ~args:A.nil
    ~ret:S.(list (obj suffix_item)) @@ fun d () ->
  let make (u : Document.unprocessed_item) = (u.kind, (u.text, ())) in
  List.map make (Document.suffix d)

let _ =
  declare ~name:"has_suffix" ~descr:"indicates whether the \
      document has a suffix (unprocessed items)" ~args:A.nil ~ret:S.bool
    @@ fun d () ->
  Document.suffix d <> []

let common_contents_args =
  A.add ~name:"include_ghost" ~descr:"indicate whether ghost commands \
    should be included" S.bool @@
  A.add ~name:"include_suffix" ~descr:"indicate whether the suffix should \
    be included" S.bool @@
  A.nil

let _ =
  let args = common_contents_args in
  declare ~name:"contents" ~descr:"gives the current contents of the \
      document, as if it was written to a file" ~args ~ret:S.string
    @@ fun d (include_ghost, (include_suffix, ())) ->
  Document.contents ~include_ghost ~include_suffix d

let _ =
  let args =
    A.add ~name:"file" ~descr:"optional target file" S.(nullable string) @@
    common_contents_args
  in
  declare_full ~name:"commit" ~descr:"write the current document \
      contents to the file, failing in case of file system error" ~args
      ~ret:S.null ~err:S.null
    @@ fun d (file, (include_ghost, (include_suffix, ()))) ->
  let res = Document.commit ?file ~include_ghost ~include_suffix d in
  Result.map_error (fun s -> (s, ())) res

let compile_result =
  let fields =
    API.Fields.add ~name:"success" S.bool @@
    API.Fields.add ~name:"stdout" S.string @@
    API.Fields.add ~name:"stderr" S.string @@
    API.Fields.add ~name:"error" ~descr:"non-null if success is false"
      S.(nullable string) @@
    API.Fields.nil
  in
  let encode (success, (stdout, (stderr, (error, ())))) =
    let ret =
      match (success, error) with
      | (true , None   ) -> Ok(())
      | (true , Some(_)) -> assert false
      | (false, Some(e)) -> Error(e)
      | (false, None   ) -> assert false
    in
    (ret, stdout, stderr)
  in
  let decode (ret, stdout, stderr) =
    match ret with
    | Ok(())       -> (true , (stdout, (stderr, (None, ()))))
    | Error(error) -> (false, (stdout, (stderr, (Some(error), ()))))
  in
  API.declare_object api ~name:"CompileResult"
    ~descr:"result of the `compile` method" ~encode ~decode fields

let _ =
  declare ~name:"compile" ~descr:"compile the current contents of \
    the file with `rocq compile`" ~args:A.nil
    ~ret:S.(obj compile_result) @@ fun d () ->
  Document.compile d

let _ =
  let args = A.add ~name:"text" ~descr:"text of the query" S.string A.nil in
  declare_full ~name:"query" ~descr:"runs the given query at \
      the cursor, not updating the state" ~args ~ret:S.(obj command_data)
    ~err:S.null @@ fun d (text, ()) ->
  let res = Document.query ~text d in
  Result.map_error (fun s -> (s, ())) res

let query_args =
  A.add ~name:"text" ~descr:"text of the query" S.string @@
  A.add ~name:"index" ~descr:"feedback item index for the result" S.int @@
  A.nil

let _ =
  declare_full ~name:"query_text" ~descr:"runs the given query at \
      the cursor, not updating the state" ~args:query_args ~ret:S.string
    ~ret_descr:"query's result, as taken from the \"info\" \ \"notice\" \
      feedback at the given index" ~err:S.null
    @@ fun d (text, (index, ())) ->
  let res = Document.query_text d ~text ~index in
  Result.map_error (fun s -> (s, ())) res

let query_all_args =
  A.add ~name:"text" ~descr:"text of the query" S.string @@
  A.add ~name:"indices" ~descr:"feedback indices to collect"
    S.(nullable (list int)) @@
  A.nil

let _ =
  declare_full ~name:"query_text_all" ~descr:"runs the given \
      query at the cursor, not updating the state" ~args:query_all_args
    ~ret:S.(list string) ~err:S.null
    @@ fun d (text, (indices, ())) ->
  let res = Document.query_text_all d ~text ?indices in
  Result.map_error (fun s -> (s, ())) res

let _ =
  declare_full ~name:"query_json" ~descr:"runs the given query at \
      the cursor, not updating the state" ~args:query_args ~ret:S.any
    ~ret_descr:"arbitrary JSON data, as returned by the query as JSON text, \
      taken from the \"info\" / \"notice\" feedback with the given index"
    ~err:S.null @@ fun d (text, (index, ())) ->
  let res = Document.query_json d ~text ~index in
  Result.map_error (fun s -> (s, ())) res

let _ =
  declare_full ~name:"query_json_all" ~descr:"runs the given \
      query at the cursor, not updating the state" ~args:query_all_args
    ~ret:S.(list any) ~err:S.null
    @@ fun d (text, (indices, ())) ->
  let res = Document.query_json_all d ~text ?indices in
  Result.map_error (fun s -> (s, ())) res

let _ =
  declare_full ~name:"materialize" ~descr:"materializes the cursor, \
    giving it its own dedicated top-level" ~args:A.nil ~ret:S.null ~err:S.null
    @@ fun d () ->
  Result.map_error (fun s -> (s, ())) (Document.materialize d)

let _ =
  declare ~name:"dump" ~descr:"dump the document contents (debug)"
    ~args:A.nil ~ret:S.any @@ fun d () ->
  Document.dump d

let _ =
  let args =
    A.add ~name:"cursor" ~descr:"the cursor to clone" S.int @@
    A.nil
  in
  API.declare api ~name:"clone" ~descr:"clones the given cursor"
    ~args ~ret:S.int ~ret_descr:"the name of the new cursor"
    @@ fun _ d (cursor, ()) ->
  let c = State.get_cursor d cursor in
  Cursor.lock c;
  let new_c = State.insert_cursor d (Cursor.make (Document.clone c.doc)) in
  Cursor.unlock c;
  new_c

let _ =
  let args =
    A.add ~name:"src" ~descr:"the source cursor" S.int @@
    A.add ~name:"dst" ~descr:"the target cursor" S.int @@
    A.nil
  in
  API.declare api ~name:"copy_contents" ~descr:"copies the contents of src \
    into dst" ~args ~ret:S.null @@ fun _ d (src, (dst, ())) ->
  let same = src = dst in
  let src = State.get_cursor d src in
  let dst = State.get_cursor d dst in
  if same then invalid_arg "source and target cursors are the same";
  Cursor.lock src;
  Cursor.lock dst;
  Document.copy_contents ~from:src.doc dst.doc;
  Cursor.unlock dst;
  Cursor.unlock src

let _ =
  let args =
    A.add ~name:"cursor" S.int @@
    A.nil
  in
  API.declare api ~name:"dispose" ~descr:"destroys the cursor"
    ~args ~ret:S.null @@ fun _ d (cursor, ()) ->
  let c = State.get_cursor d cursor in
  Cursor.lock c; (* We never unlock stopped cursors. *)
  Document.stop c.doc

type config = {
  workers : int option;
  file : string;
  args : string list;
}

let parse_args : argv:string array -> config = fun ~argv ->
  let (argv, args) = Rocq_args.split ~argv in
  let (workers, file) =
    let usage () =
      panic "Usage: %s [--workers N] FILE.v [-- ROCQ ARGS]" argv.(0)
    in
    match argv with
    | [|_; file|] -> (None, file)
    | [|_; "--workers"; workers; file|] ->
        let workers = try int_of_string workers with Failure(_) -> usage () in
        (Some(workers), file)
    | _ -> usage ()
  in
  if not (Filename.check_suffix file ".v") then
    panic "Error: a Rocq source file was expected as argument.";
  {workers; file; args}

let _ =
  match Sys.argv with
  | [|_; "--api-docs"  |] ->
      Printf.printf "%a%!" API.output_docs api;
      exit 0
  | [|_; "--python-api"|] ->
      Printf.printf "%a%!" API.output_python_api api;
      exit 0
  | _                     ->
  let {workers; file; args} = parse_args ~argv:Sys.argv in
  let state =
    let doc =
      try Document.init ~args ~file with Failure(s) -> panic "Error: %s." s
    in
    State.create doc
  in
  let run =
    match workers with
    | None -> API.run_seq
    | Some(workers) -> API.run ~workers
  in
  match run api ~ic:stdin ~oc:stdout state with
  | Ok(_)       -> exit 0
  | Error(s)    -> panic "%s" s
  | exception e ->
      panic "Error: uncaught exception.\n%s" (Printexc.to_string e)

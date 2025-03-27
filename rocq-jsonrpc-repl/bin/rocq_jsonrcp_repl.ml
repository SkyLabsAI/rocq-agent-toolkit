(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type state = Vernac.State.t

type json = Yojson.Safe.t

module Feed : sig
  type t = Feedback.feedback

  val reset : unit -> unit
  val collect : (t -> 'a option) -> 'a list

  val with_feeder : (unit -> unit) -> unit
end = struct
  type t = Feedback.feedback

  let feedback : t list ref = ref []

  let reset : unit -> unit = fun _ ->
    feedback := []

  let collect : (t -> 'a option) -> 'a list = fun f ->
    let rec filter acc xs =
      match xs with
      | []      -> acc
      | x :: xs ->
      match f x with
      | None    -> filter acc xs
      | Some(v) -> filter (v :: acc) xs
    in
    filter [] !feedback

  let feeder : Feedback.feedback -> unit = fun fb ->
    feedback := fb :: !feedback

  let with_feeder : (unit -> unit) -> unit = fun f ->
    let feeder = Feedback.add_feeder feeder in
    f (); Feedback.del_feeder feeder
end

let feedback_filter : Feed.t -> json option = fun fb ->
  let open Feedback in
  let string_of_level level =
    match level with
    | Debug   -> "debug"
    | Info    -> "info"
    | Notice  -> "notice"
    | Warning -> "warning"
    | Error   -> "error"
  in
  let to_json level loc pp =
    let text = Pp.string_of_ppcmds pp in
    let items = ("text", `String(text)) :: [] in
    let items =
      match loc with 
      | None      -> items
      | Some(loc) -> ("loc", Rocq_loc.to_json loc) :: items
    in
    let items = ("kind", `String(string_of_level level)) :: items in
    `Assoc(items)
  in
  match fb.contents with
  | Message(Debug, _  , _, _ ) -> None
  | Message(level, loc, _, pp) -> Some(to_json level loc pp)
  | _                          -> None

let rset = Jsonrpc_tp_loop.create ()

module P = Jsonrpc_tp_loop.Params

let add_handler name pspec a =
  let a s p = let (s, j) = a s p in (s, Ok(j)) in
  Jsonrpc_tp_loop.add rset name pspec a

let run_cmd : state -> (state -> json option * state) -> state * json =
    fun state run ->
  Feed.reset ();
  try
    let (data, end_state) = run state in
    let feedback = Feed.collect feedback_filter in
    let success = ("success", `Bool(true)) in
    let state =
      let sid = Stm.get_current_state ~doc:end_state.doc in
      ("state", `Int(Stateid.to_int sid))
    in
    let data =
      match data with
      | None       -> []
      | Some(json) -> [("data", json)]
    in
    let feedback =
      match feedback with
      | [] -> []
      | _  -> [("feedback", `List(feedback))]
    in
    let fields = success :: state :: data @ feedback in
    (end_state, `Assoc(fields))
  with e ->
    let (e, info) = Exninfo.capture e in
    let loc = Loc.get_loc info in
    let pp = CErrors.iprint (e, info) in
    let feedback = Feed.collect feedback_filter in
    let success = ("success", `Bool(false)) in
    let sid =
      let sid = Stm.get_current_state ~doc:state.doc in
      ("state", `Int(Stateid.to_int sid))
    in
    let error = ("error", `String(Pp.string_of_ppcmds pp)) in
    let loc =
      match loc with
      | None      -> []
      | Some(loc) -> [("loc", Rocq_loc.to_json loc)]
    in
    let feedback =
      match feedback with
      | [] -> []
      | _  -> [("feedback", `List(feedback))]
    in
    let fields = success :: sid :: error :: loc @ feedback in
    (state, `Assoc(fields))

let _ =
  let pspec = P.(cons int nil) in
  add_handler "back_to" pspec @@ fun state (sid, ()) ->
  run_cmd state @@ fun state ->
  let sid = Stateid.of_int sid in
  let (doc, _) = Stm.edit_at ~doc:state.doc sid in
  (None, {state with doc; sid})

let _ =
  let pspec = P.(cons int (cons int nil)) in
  add_handler "show_goal" pspec @@ fun state (gid, (sid, ())) ->
  run_cmd state @@ fun state ->
  let sid = Stateid.of_int sid in
  let proof = Stm.get_proof ~doc:state.doc sid in
  let goal = Printer.pr_goal_emacs ~proof gid (Stateid.to_int sid) in
  let data = `String(Pp.string_of_ppcmds goal) in
  (Some(data), state)

let _ =
  let pspec = P.(cons int (cons string nil)) in
  add_handler "run" pspec @@ fun state (off, (text, ())) ->
  run_cmd state @@ fun state ->
  let stream = Gramlib.Stream.of_string ~offset:off text in
  let input = Procq.Parsable.make stream in
  let entry = Pvernac.main_entry in
  let open Vernac.State in
  match Stm.parse_sentence ~doc:state.doc state.sid ~entry input with
  | None         ->
      CErrors.user_err (Pp.str "End of file, no command found in input.")
  | Some(vernac) ->
  let new_state = Vernac.process_expr ~state vernac in
  let goal = Option.map Printer.pr_open_subgoals new_state.proof in
  let data = Option.map (fun pp -> `String(Pp.string_of_ppcmds pp)) goal in
  (data, new_state)

let loop : state -> unit = fun state ->
  try ignore (Jsonrpc_tp_loop.run rset ~ic:stdin ~oc:stdout state) with
  | Jsonrpc_tp_loop.Error(s) ->
      Printf.eprintf "Error: %s.\n%!" s
  | Sys_error(s)             ->
      Printf.eprintf "Error: %s.\n%!" s

let run _ ~opts:_ state =
  Feed.with_feeder @@ fun _ ->
  Flags.without_option Flags.in_ml_toplevel loop state

let init_document opts injections =
  Flags.load_vos_libraries := true;
  let (doc, sid) =
    let toplevel_name = opts.Coqargs.config.logic.toplevel_name in
    let doc_type = Stm.Interactive(toplevel_name) in
    Stm.new_doc {doc_type; injections}
  in
  let time = Option.map Vernac.make_time_output opts.config.time in
  Vernac.State.{doc; sid; proof = None; time}

let init_toploop opts _ injections =
  let state = init_document opts injections in
  Load.load_init_vernaculars opts ~state

let init_extra ((), async_opts) injections ~opts =
  init_toploop opts async_opts injections

let parse_extra opts extras =
  let (async_opts, extras) = Stmargs.parse_args opts extras in
  ((), async_opts), extras

let _ =
  let args = List.tl (Array.to_list Sys.argv) in
  let usage =
    let executable_name = "rocq_simple_repl" in
    Boot.Usage.{executable_name; extra_args = ""; extra_options = ""}
  in
  let coqtop_toplevel =
    let initial_args = Coqargs.default in
    Coqtop.{parse_extra; usage; init_extra; run; initial_args}
  in
  Coqtop.start_coq coqtop_toplevel args

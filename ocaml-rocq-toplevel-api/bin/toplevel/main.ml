open Rocq_toplevel_data

type state = Vernac.State.t

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

let feedback_filter : Feed.t -> feedback_message option = fun fb ->
  let open Feedback in
  let make level loc quickfix pp =
    let text = Pp.string_of_ppcmds pp in
    let quickfix =
      let make f =
        let loc = Quickfix.loc f in
        let text = Pp.string_of_ppcmds (Quickfix.pp f) in
        {loc; text}
      in
      List.map make quickfix
    in
    {level; loc; quickfix; text}
  in
  match fb.contents with
  | Message(Debug, _  , _       , _ ) -> None
  | Message(level, loc, quickfix, pp) -> Some(make level loc quickfix pp)
  | _                                 -> None

let is_require : Vernacexpr.vernac_control -> bool = fun vernac ->
  let open Vernacexpr in
  match vernac.CAst.v.expr with
  | VernacSynterp(VernacRequire(_,_,_)) -> true
  | VernacSynterp(_) -> false
  | VernacSynPure(_) -> false

let globrefs_diff : Environ.env -> Environ.env -> globrefs_diff =
    fun env1 env2 ->
  let open Environ.Internal.View in
  let {env_constants = c1; env_inductives = i1; _} = view env1 in
  let {env_constants = c2; env_inductives = i2; _} = view env2 in
  let f k v1 v2 ((removed_cs, added_cs) as cs) =
    match (v1, v2) with
    | (None   , None   ) -> assert false
    | (Some(_), None   ) -> (k :: removed_cs, added_cs)
    | (None   , Some(_)) -> (removed_cs, k :: added_cs)
    | (Some(_), Some(_)) -> cs (* May occur on, e.g., section closing. *)
  in
  let (removed_constants, added_constants) =
    Names.Cmap_env.symmetric_diff_fold f c1 c2 ([], [])
  in
  let (removed_inductives, added_inductives) =
    Names.Mindmap_env.symmetric_diff_fold f i1 i2 ([], [])
  in
  {added_constants; removed_constants; added_inductives; removed_inductives}

let back_to state sid =
  try
    let sid = Stateid.of_int sid in
    let (doc, _) = Stm.edit_at ~doc:state.Vernac.State.doc sid in
    (Vernac.State.{state with doc; sid}, Ok(()))
  with e ->
    let pp = CErrors.iprint (Exninfo.capture e) in
    (state, Error(Pp.string_of_ppcmds pp))

(* Hack around the lack of standalone subgoal printing. *)
let fixup_subgoal : Pp.t -> Pp.t = fun p ->
  let open Pp in
  let exception Fallback in
  let rec decomp rest =
    match rest with
    | [] :: rest -> decomp rest
    | (v :: vs) :: rest -> (v, vs :: rest)
    | [] -> raise Fallback
  in
  let rec find found_is (p, rest) =
    match repr p with
    | Ppcmd_glue(p :: ps) -> find found_is (p, ps :: rest)
    | Ppcmd_string(" is:") when not found_is ->
        find true (decomp rest)
    | Ppcmd_box(_,_) when found_is -> p
    | _ -> find found_is (decomp rest)
  in
  try
    match repr p with
    | Ppcmd_box(_,p) -> find false (p, [])
    | _ -> raise Fallback
  with Fallback -> p

let run state off text =
  Feed.reset ();
  try
    let stream = Gramlib.Stream.of_string ~offset:off text in
    let input = Procq.Parsable.make stream in
    let entry = Pvernac.main_entry in
    let open Vernac.State in
    let vernac =
      match Stm.parse_sentence ~doc:state.doc state.sid ~entry input with
      | Some(vernac) -> vernac
      | None         ->
          CErrors.user_err (Pp.str "End of file, no command found in input.")
    in
    let env1 = Global.env () in
    let new_state = Vernac.process_expr ~state vernac in
    let env2 = Global.env () in
    let data =
      let globrefs_diff =
        match is_require vernac with
        | true  -> empty_globrefs_diff
        | false -> globrefs_diff env1 env2
      in
      let proof_state =
        match new_state.proof with None -> None | Some(proof) ->
        let Proof.{goals; stack; sigma; _} = Proof.data proof in
        let given_up_goals = Evar.Set.cardinal (Evd.given_up sigma) in
        let shelved_goals = List.length (Evd.shelf sigma) in
        let unfocused_goals =
          let make (l, r) = List.length l + List.length r in
          List.map make stack
        in
        let focused_goals =
          let make i _ =
            let p = Printer.pr_nth_open_subgoal ~proof (i + 1) in
            Pp.string_of_ppcmds (fixup_subgoal p)
          in
          List.mapi make goals
        in
        Some({given_up_goals; shelved_goals; unfocused_goals; focused_goals})
      in
      let feedback_messages = Feed.collect feedback_filter in
      {globrefs_diff; feedback_messages; proof_state}
    in
    (new_state, Ok(data))
  with e ->
    let (e, info) = Exninfo.capture e in
    let error_loc = Loc.get_loc info in
    let msg = Pp.string_of_ppcmds (CErrors.iprint (e, info)) in
    let feedback_messages = Feed.collect feedback_filter in
    (state, Error(msg, {error_loc; feedback_messages}))

let fork : state -> pipe_in:string -> pipe_out:string ->
    state * (int, string) result = fun state ~pipe_in ~pipe_out ->
  let setup () =
    try
      let stdin_fd = Unix.descr_of_in_channel stdin in
      let stdout_fd = Unix.descr_of_out_channel stdout in
      let ifd = Unix.openfile pipe_in [Unix.O_RDONLY] 0o600 in
      let ofd = Unix.openfile pipe_out [Unix.O_WRONLY] 0o600 in
      Unix.dup2 ifd stdin_fd;
      Unix.dup2 ofd stdout_fd;
      Ok(0)
    with Unix.Unix_error(_,_,_) ->
      assert false (* Not much we can do if pipes are broken... *)
  in
  try
    match Unix.fork () with
    | 0   -> (state, setup ())
    | pid -> (state, Ok(pid) )
  with Unix.Unix_error(e,_,_) ->
    (state, Error(Unix.error_message e))

let run_command : type r e. state -> (r, e) command -> state * (r, e) result =
    fun state c ->
  match c with
  | Run({off; text})          -> run state off text
  | BackTo({sid})             -> back_to state sid
  | Fork({pipe_in; pipe_out}) -> fork state ~pipe_in ~pipe_out

let interact : state -> unit = fun state ->
  let pid = Unix.getpid () in
  Marshal.to_channel stdout (pid, Stateid.to_int state.Vernac.State.sid) [];
  Out_channel.flush stdout;
  let rec loop state =
    let c = Marshal.from_channel stdin in
    let (state, r) = run_command state c in
    Marshal.to_channel stdout (state.Vernac.State.sid, r) [];
    Out_channel.flush stdout;
    loop state
  in
  try loop state with
  | End_of_file  -> ()
  | Sys_error(s) -> Printf.eprintf "Error: %s.\n%!" s; exit 1

let run _ ~opts:_ state =
  Feed.with_feeder @@ fun _ ->
  Flags.without_option Flags.in_ml_toplevel interact state

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

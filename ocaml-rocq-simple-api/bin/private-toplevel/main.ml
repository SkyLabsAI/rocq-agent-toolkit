open Rocq_simple_api_internal
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

let structured_goal_of_evar : Evd.evar_map -> Evar.t -> structured_goal =
    fun sigma ev ->
  let evi = Evd.find_undefined sigma ev in
  let env = Evd.evar_filtered_env (Global.env ()) evi in
  let pr c = Pp.string_of_ppcmds (Printer.pr_leconstr_env env sigma c) in
  let pr_type ?goal_concl_style t =
    Pp.string_of_ppcmds (Printer.pr_letype_env ?goal_concl_style env sigma t)
  in
  let open Context.Named.Declaration in
  let hyp_of_decl d =
    let name = Names.Id.to_string (get_id d) in
    let def = Option.map pr (get_value d) in
    {name; def; hyp_type = pr_type (get_type d)}
  in
  let hyps = List.rev_map hyp_of_decl (Evd.evar_filtered_context evi) in
  {hyps; goal = pr_type ~goal_concl_style:true (Evd.evar_concl evi)}

let structured_goals state =
  let get_goals proof =
    let Proof.{goals; sigma; _} = Proof.data proof in
    List.map (structured_goal_of_evar sigma) goals
  in
  Option.map get_goals state.Vernac.State.proof

let run state input_loc text =
  Feed.reset ();
  let error ?loc e =
    let (e, info) = Exninfo.capture e in
    let error_loc = Loc.get_loc info in
    let msg = Pp.string_of_ppcmds (CErrors.iprint (e, info)) in
    let feedback_messages = Feed.collect feedback_filter in
    Error(msg, {error_loc; feedback_messages; loc})
  in
  let run () =
    let stream = Gramlib.Stream.of_string ~offset:input_loc.Loc.bp text in
    let input = Procq.Parsable.make ~loc:input_loc stream in
    let entry = Pvernac.main_entry in
    let open Vernac.State in
    let vernac =
      match Stm.parse_sentence ~doc:state.doc state.sid ~entry input with
      | Some(vernac) -> vernac
      | None         ->
          CErrors.user_err (Pp.str "End of file, no command found in input.")
    in
    match vernac.CAst.loc with None -> assert false | Some(loc) ->
    (* Check for leading text. *)
    let len_leading = loc.Loc.bp - input_loc.Loc.bp in
    if len_leading <> 0 then begin
      let s = String.sub text 0 len_leading in
      let msg = Printf.sprintf "Leading text before command: %S." s in
      CErrors.user_err (Pp.str msg)
    end;
    (* Check for trailing text. *)
    let len_command = loc.Loc.ep - loc.Loc.bp in
    let len_text = String.length text in
    if len_command < len_text then begin
      let s = String.sub text len_command (len_text - len_command) in
      let msg = Printf.sprintf "Trailing text after command: %S." s in
      CErrors.user_err (Pp.str msg)
    end;
    Ok(vernac)
  in
  match run () with
  | exception e   -> (state, error e)
  | Error(result) -> result
  | Ok(vernac)    ->
  let loc = vernac.CAst.loc in
  try
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
      let synterp_ast = Rocq_vernac_entry.of_vernac_control vernac in
      {globrefs_diff; feedback_messages; synterp_ast; proof_state; loc}
    in
    (new_state, Ok(data))
  with e ->
    (* Data collection error treated as command failure (rollback state). *)
    let res = error ?loc e in
    let sid = Stateid.to_int state.Vernac.State.sid in
    let state = fst (back_to state sid) in
    (state, res)

let loc_after_blanks loc text =
  let module State = CLexer.Lexer.State in
  let saved_state = State.get () in
  State.set (State.init ());
  Fun.protect ~finally:(fun () -> State.set saved_state) @@ fun () ->
  try
    let chars = Gramlib.Stream.of_string ~offset:loc.Loc.bp text in
    let tokens = CLexer.Lexer.tok_func ~loc chars in
    let keywords = Procq.get_keyword_state () in
    match Gramlib.LStream.next keywords tokens with
    | Some(Tok.EOI) ->
        let loc = Gramlib.LStream.current_loc tokens in
        Ok(Loc.create loc.fname loc.line_nb loc.bol_pos loc.bp loc.bp)
    | Some(tok) ->
        let tok = Tok.extract_string false tok in
        let msg =
          Printf.sprintf "Expected only blank characters and comments, but \
            found token %S." tok
        in
        Error(msg)
    | None -> assert false
  with e ->
    let pp = CErrors.iprint (Exninfo.capture e) in
    Error(Pp.string_of_ppcmds pp)

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

(* Splitting the given text without attempting to restore the state. *)
let destructive_split state sid loc text =
  Feed.reset ();
  let rev_commands = ref [] in
  let synterp_state () =
    let err s = CErrors.user_err (Pp.str s) in
    let state =
      match sid with None -> state | Some(sid) ->
      let (state, res) = back_to state sid in
      match res with Ok(()) -> state | Error(_) ->
      err "The given Rocq state could not be reached."
    in
    let get () = Stm.state_of_id ~doc:state.Vernac.State.doc state.sid in
    match get () with
    | Stm.Valid(Some(vs)) -> vs.Vernacstate.synterp
    | Stm.Expired         -> err "The current Rocq state has expired."
    | Stm.Error(e)        -> raise e
    | Stm.Valid(None)     ->
    Stm.observe ~doc:state.doc state.sid;
    match get () with
    | Stm.Valid(Some(vs)) -> vs.Vernacstate.synterp
    | Stm.Valid(None)     -> err "The current Rocq state is not available."
    | Stm.Expired         -> err "The current Rocq state has expired."
    | Stm.Error(e)        -> raise e
  in
  let result =
    try
      Vernacstate.Synterp.unfreeze (synterp_state ());
      let stream = Gramlib.Stream.of_string ~offset:loc.Loc.bp text in
      let input = Procq.Parsable.make ~loc stream in
      let rec loop () =
        let mode = Some(Synterp.get_default_proof_mode ()) in
        match Procq.Entry.parse (Pvernac.main_entry mode) input with
        | None    -> Ok(())
        | Some(c) ->
        let c = Synterp.synterp_control ~intern:Vernacinterp.fs_intern c in
        let c = Rocq_vernac_entry.of_vernac_control_entry c in
        rev_commands := c :: !rev_commands;
        loop ()
      in
      loop ()
    with e ->
      let (e, info) = Exninfo.capture e in
      let msg = Pp.string_of_ppcmds (CErrors.iprint (e, info)) in
      Error(msg, Loc.get_loc info)
  in
  let commands = List.rev !rev_commands in
  let feedback = Feed.collect (fun fb -> Some(fb)) in
  {commands; feedback; result}

(* Forks to protect the main toplevel state from bad interference. *)
let split state sid loc text =
  let failure msg =
    let msg = "Could not run the sentence-splitter: " ^ msg in
    {commands = []; feedback = []; result = Error(msg, None)}
  in
  match Unix.pipe () with
  | exception Unix.Unix_error(e,_,_) -> failure (Unix.error_message e)
  | (read_fd, write_fd) ->
  let run_child () =
    (* Exit on all exceptions. *)
    (fun f -> try f () with _ -> Unix._exit 2) @@ fun () ->
    (* Disconnect stdout/stderr to not mess with the toplevel protocol. *)
    let null = Unix.openfile "/dev/null" [Unix.O_WRONLY] 0 in
    Unix.dup2 null (Unix.descr_of_out_channel stdout);
    Unix.dup2 null (Unix.descr_of_out_channel stderr);
    Unix.close null;
    (* Do the splitting. *)
    let result = destructive_split state sid loc text in
    (* Write the result to the pipe. *)
    let oc = Unix.close read_fd; Unix.out_channel_of_descr write_fd in
    Marshal.to_channel oc result []; Out_channel.flush oc;
    Out_channel.close_noerr oc; Unix._exit 0
  in
  let run_parent pid =
    match Unix.close write_fd; Unix.in_channel_of_descr read_fd with
    | exception Unix.Unix_error(e,_,_) -> failure (Unix.error_message e)
    | ic ->
    let res = try Some(Marshal.from_channel ic) with _ -> None in
    In_channel.close_noerr ic;
    match snd (Unix.waitpid [] pid) with
    | exception Unix.Unix_error(e,_,_) -> failure (Unix.error_message e)
    | Unix.WEXITED(0) -> assert (res <> None); Option.get res
    | Unix.WEXITED(n) ->
        failure (Printf.sprintf "child process exited with code %i" n)
    | Unix.WSIGNALED(n) ->
        failure (Printf.sprintf "child process was killed by signal %i" n)
    | Unix.WSTOPPED(n) ->
        failure (Printf.sprintf "child process was stopped by signal %i" n)
  in
  match Unix.fork () with
  | exception Unix.Unix_error(e,_,_) ->
      Unix.close read_fd; Unix.close write_fd; failure (Unix.error_message e)
  | 0 -> run_child ()
  | pid -> run_parent pid

let run_cmd : type r e. state -> (r, e) cmd ->
    state * (r, e) result = fun state c ->
  match c with
  | Run({loc; text})            -> run state loc text
  | BackTo({sid})               -> back_to state sid
  | Fork({pipe_in; pipe_out})   -> fork state ~pipe_in ~pipe_out
  | StructuredGoals             -> (state, Ok(structured_goals state))
  | LocAfterBlanks({loc; text}) -> (state, loc_after_blanks loc text)
  | Split({loc; text; sid})     -> (state, Ok(split state sid loc text))

let interact : state -> unit = fun state ->
  let pid = Unix.getpid () in
  Marshal.to_channel stdout (pid, Stateid.to_int state.Vernac.State.sid) [];
  Out_channel.flush stdout;
  let rec loop state =
    let c = Marshal.from_channel stdin in
    let (state, r) = run_cmd state c in
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

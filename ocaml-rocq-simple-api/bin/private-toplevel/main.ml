open Rocq_simple_api_internal
open Rocq_toplevel_data

type state = Vernac.State.t

let block_sigint () =
  ignore (Unix.sigprocmask SIG_BLOCK [Sys.sigint])

let unblock_sigint () =
  ignore (Unix.sigprocmask SIG_UNBLOCK [Sys.sigint])

let () =
  ignore (Unix.setsid ());
  block_sigint ()

let send_control_ack ack =
  Marshal.to_channel stdout ack [];
  Out_channel.flush stdout

let rec waitpid pid =
  try snd (Unix.waitpid [] pid) with
  | Unix.Unix_error(EINTR, _, _) -> waitpid pid

let kill_pid pid signal =
  try Unix.kill pid signal with Unix.Unix_error(_,_,_) -> ()

let kill_group pid signal =
  try Unix.kill (-pid) signal with Unix.Unix_error(_,_,_) -> ()

let terminate_child pid =
  kill_group pid Sys.sigkill;
  kill_pid pid Sys.sigkill

exception Fork_child of state

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
  with
  | Sys.Break -> raise Sys.Break
  | e ->
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
  | exception Sys.Break -> raise Sys.Break
  | exception e         -> (state, error e)
  | Error(result)       -> result
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
  with
  | Sys.Break -> raise Sys.Break
  | e ->
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
  with
  | Sys.Break -> raise Sys.Break
  | e ->
      let pp = CErrors.iprint (Exninfo.capture e) in
      Error(Pp.string_of_ppcmds pp)

let close_fd_noerr fd =
  try Unix.close fd with Unix.Unix_error(_,_,_) -> ()

let setup_fork_child state ~pipe_in ~pipe_out =
  try
    ignore (Unix.setsid ());
    let stdin_fd = Unix.descr_of_in_channel stdin in
    let stdout_fd = Unix.descr_of_out_channel stdout in
    let ifd = Unix.openfile pipe_in [Unix.O_RDONLY] 0o600 in
    let ofd = Unix.openfile pipe_out [Unix.O_WRONLY] 0o600 in
    Unix.dup2 ifd stdin_fd;
    Unix.dup2 ofd stdout_fd;
    Unix.close ifd;
    Unix.close ofd;
    raise (Fork_child state)
  with
  | Fork_child(_) as e -> raise e
  | _ -> Unix._exit 2

let disconnect_supervisor_protocol () =
  let stdin_fd = Unix.descr_of_in_channel stdin in
  let stdout_fd = Unix.descr_of_out_channel stdout in
  let ifd = Unix.openfile "/dev/null" [Unix.O_RDONLY] 0 in
  let ofd = Unix.openfile "/dev/null" [Unix.O_WRONLY] 0 in
  Unix.dup2 ifd stdin_fd;
  Unix.dup2 ofd stdout_fd;
  Unix.close ifd;
  Unix.close ofd

(* Keep the actual top-level as an unreaped child until its API owner releases
   it, so its PID cannot be reused while the handle is still live. *)
let run_fork_supervisor state ~pipe_in ~pipe_out ~pipe_supervisor pid_fd =
  try
    ignore (Unix.setsid ());
    disconnect_supervisor_protocol ();
    let supervisor_fd =
      Unix.openfile pipe_supervisor [Unix.O_RDONLY] 0o600
    in
    match Unix.fork () with
    | exception Unix.Unix_error(_,_,_) ->
        Unix.close supervisor_fd;
        Unix.close pid_fd;
        Unix._exit 2
    | 0 ->
        Unix.close supervisor_fd;
        Unix.close pid_fd;
        setup_fork_child state ~pipe_in ~pipe_out
    | child_pid ->
        try
          let pid_oc = Unix.out_channel_of_descr pid_fd in
          Marshal.to_channel pid_oc child_pid [];
          Out_channel.flush pid_oc;
          Out_channel.close_noerr pid_oc;
          let supervisor_ic = Unix.in_channel_of_descr supervisor_fd in
          let control =
            try Some(Marshal.from_channel supervisor_ic : supervisor_control)
            with _ -> None
          in
          In_channel.close_noerr supervisor_ic;
          begin match control with
          | Some(Supervisor_stop) -> ()
          | Some(Supervisor_kill) | None -> terminate_child child_pid
          end;
          ignore (waitpid child_pid);
          Unix._exit 0
        with _ ->
          close_fd_noerr pid_fd;
          close_fd_noerr supervisor_fd;
          terminate_child child_pid;
          (try ignore (waitpid child_pid) with _ -> ());
          Unix._exit 2
  with
  | Fork_child(_) as e -> raise e
  | _ ->
      close_fd_noerr pid_fd;
      Unix._exit 2

(* Double-fork so the long-lived supervisor is independent from the source
   top-level and is reaped by the operating system's child reaper. *)
let launch_supervised_child state ~pipe_in ~pipe_out ~pipe_supervisor =
  let (pid_in, pid_out) = Unix.pipe ~cloexec:true () in
  match Unix.fork () with
  | exception Unix.Unix_error(e,_,_) ->
      Unix.close pid_in;
      Unix.close pid_out;
      Error(Unix.error_message e)
  | 0 ->
      Unix.close pid_in;
      begin match Unix.fork () with
      | exception Unix.Unix_error(_,_,_) -> Unix._exit 2
      | 0 ->
          run_fork_supervisor
            state ~pipe_in ~pipe_out ~pipe_supervisor pid_out
      | _ ->
          Unix.close pid_out;
          Unix._exit 0
      end
  | launcher_pid ->
      Unix.close pid_out;
      let launcher_status = waitpid launcher_pid in
      let pid_ic = Unix.in_channel_of_descr pid_in in
      let child_pid =
        try Some(Marshal.from_channel pid_ic : int) with _ -> None
      in
      In_channel.close_noerr pid_ic;
      begin match (launcher_status, child_pid) with
      | (Unix.WEXITED(0), Some(pid)) -> Ok(pid)
      | (Unix.WEXITED(0), None) ->
          Error("fork supervisor failed to start")
      | (Unix.WEXITED(n), _) ->
          Error(Printf.sprintf "fork launcher exited with code %i" n)
      | (Unix.WSIGNALED(n), _) ->
          Error(Printf.sprintf "fork launcher was killed by signal %i" n)
      | (Unix.WSTOPPED(n), _) ->
          Error(Printf.sprintf "fork launcher was stopped by signal %i" n)
      end

let fork : state -> pipe_in:string -> pipe_out:string ->
    pipe_supervisor:string -> state * (int, string) result =
    fun state ~pipe_in ~pipe_out ~pipe_supervisor ->
  let previous_mask = Unix.sigprocmask SIG_BLOCK [Sys.sigint] in
  let restore_mask () =
    ignore (Unix.sigprocmask SIG_SETMASK previous_mask)
  in
  match launch_supervised_child state ~pipe_in ~pipe_out ~pipe_supervisor with
  | exception (Fork_child(_) as e) -> raise e
  | exception e -> restore_mask (); raise e
  | Error(error) -> restore_mask (); (state, Error(error))
  | Ok(pid) ->
      try restore_mask (); (state, Ok(pid)) with Sys.Break ->
        terminate_child pid;
        raise Sys.Break

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
    with
    | Sys.Break -> raise Sys.Break
    | e ->
        let (e, info) = Exninfo.capture e in
        let msg = Pp.string_of_ppcmds (CErrors.iprint (e, info)) in
        Error(msg, Loc.get_loc info)
  in
  let commands = List.rev !rev_commands in
  let feedback = Feed.collect (fun fb -> Some(fb)) in
  {commands; feedback; result}

(* Forks to protect the main toplevel state from bad interference. *)
let split state sid loc text =
  let previous_mask = Unix.sigprocmask SIG_BLOCK [Sys.sigint] in
  let restore_mask () =
    ignore (Unix.sigprocmask SIG_SETMASK previous_mask)
  in
  let failure msg =
    let msg = "Could not run the sentence-splitter: " ^ msg in
    {commands = []; feedback = []; result = Error(msg, None)}
  in
  match Unix.pipe ~cloexec:true () with
  | exception Unix.Unix_error(e,_,_) ->
      restore_mask ();
      failure (Unix.error_message e)
  | (read_fd, write_fd) ->
  let run_child () =
    (* Exit on all exceptions before restoring the interrupt mask. *)
    (fun f -> try f () with _ -> Unix._exit 2) @@ fun () ->
    (* Isolate the inherited top-level protocol descriptors. *)
    let null_in =
      Unix.openfile "/dev/null" [Unix.O_RDONLY; Unix.O_CLOEXEC] 0
    in
    let null_out =
      Unix.openfile "/dev/null" [Unix.O_WRONLY; Unix.O_CLOEXEC] 0
    in
    Unix.dup2 null_in (Unix.descr_of_in_channel stdin);
    Unix.dup2 null_out (Unix.descr_of_out_channel stdout);
    Unix.dup2 null_out (Unix.descr_of_out_channel stderr);
    Unix.close null_in;
    Unix.close null_out;
    Unix.close read_fd;
    let oc = Unix.out_channel_of_descr write_fd in
    (* Only now can interruption safely escape in the splitter child. *)
    restore_mask ();
    let result = destructive_split state sid loc text in
    Marshal.to_channel oc result [];
    Out_channel.flush oc;
    Out_channel.close_noerr oc;
    Unix._exit 0
  in
  let run_parent pid =
    let read_fd_owned = ref true in
    let write_fd_owned = ref true in
    let ic = ref None in
    let reaped = ref false in
    let close_read_fd () =
      if !read_fd_owned then begin
        read_fd_owned := false;
        close_fd_noerr read_fd
      end
    in
    let close_write_fd () =
      if !write_fd_owned then begin
        write_fd_owned := false;
        close_fd_noerr write_fd
      end
    in
    let close_ic () =
      match !ic with
      | None -> ()
      | Some(channel) -> ic := None; In_channel.close_noerr channel
    in
    let cleanup_child () =
      close_ic ();
      close_read_fd ();
      close_write_fd ();
      if not !reaped then begin
        terminate_child pid;
        ignore (waitpid pid);
        reaped := true
      end
    in
    try
      (* The parent owns every resource before any operation can fail. *)
      close_write_fd ();
      let channel = Unix.in_channel_of_descr read_fd in
      read_fd_owned := false;
      ic := Some(channel);
      restore_mask ();
      let res =
        try Some(Marshal.from_channel channel) with
        | Sys.Break -> raise Sys.Break
        | _ -> None
      in
      close_ic ();
      let status = waitpid pid in
      reaped := true;
      match status with
      | Unix.WEXITED(0) -> assert (res <> None); Option.get res
      | Unix.WEXITED(n) ->
          failure (Printf.sprintf "child process exited with code %i" n)
      | Unix.WSIGNALED(n) ->
          failure (Printf.sprintf "child process was killed by signal %i" n)
      | Unix.WSTOPPED(n) ->
          failure (Printf.sprintf "child process was stopped by signal %i" n)
    with
    | Sys.Break ->
        block_sigint ();
        cleanup_child ();
        raise Sys.Break
    | e ->
        block_sigint ();
        cleanup_child ();
        raise e
  in
  match Unix.fork () with
  | exception Unix.Unix_error(e,_,_) ->
      Unix.close read_fd;
      Unix.close write_fd;
      restore_mask ();
      failure (Unix.error_message e)
  | 0 -> run_child ()
  | pid -> run_parent pid

let run_cmd : type r e. state -> (r, e) cmd ->
    state * (r, e) result = fun state c ->
  match c with
  | Run({loc; text}) -> run state loc text
  | BackTo({sid}) -> back_to state sid
  | Fork({pipe_in; pipe_out; pipe_supervisor}) ->
      fork state ~pipe_in ~pipe_out ~pipe_supervisor
  | StructuredGoals -> (state, Ok(structured_goals state))
  | LocAfterBlanks({loc; text}) -> (state, loc_after_blanks loc text)
  | Split({loc; text; sid}) -> (state, Ok(split state sid loc text))

type ('result, 'error) execution =
  | Execution_completed of state * ('result, 'error) result
  | Execution_interrupted of state

let rollback state =
  let sid = Stateid.to_int state.Vernac.State.sid in
  match back_to state sid with
  | (state, Ok(())) -> state
  | (_, Error(message)) ->
      failwith ("could not restore the pre-request state: " ^ message)

let cleanup_completed : type r e. (r, e) cmd -> (r, e) result -> unit =
    fun command result ->
  match (command, result) with
  | (Fork(_), Ok(pid)) -> terminate_child pid
  | _ -> ()

let finish_cancel_signal request_id =
  match (Marshal.from_channel stdin : control) with
  | Cancel_signal_sent(id) when id = request_id ->
      if List.mem Sys.sigint (Unix.sigpending ()) then
        ignore (Unix.sigwait [Sys.sigint])
  | _ -> failwith "mismatched cancellation signal fence"

let run_request : type r e. state -> (r, e) request -> state =
    fun initial_state {request_id; command} ->
  Marshal.to_channel stdout (Started request_id : (r, e) message) [];
  Out_channel.flush stdout;
  let execution =
    try
      if command_is_interruptible command then unblock_sigint ();
      let (state, result) = run_cmd initial_state command in
      block_sigint ();
      Execution_completed(state, result)
    with
    | Sys.Break ->
        block_sigint ();
        Execution_interrupted(rollback initial_state)
    | e ->
        block_sigint ();
        raise e
  in
  let response =
    match execution with
    | Execution_completed(state, result) ->
        let sid = Stateid.to_int state.Vernac.State.sid in
        Completed({request_id; sid; result})
    | Execution_interrupted(state) ->
        let sid = Stateid.to_int state.Vernac.State.sid in
        Interrupted({request_id; sid})
  in
  Marshal.to_channel stdout (Finished response : (r, e) message) [];
  Out_channel.flush stdout;
  let decision = (Marshal.from_channel stdin : control) in
  match (decision, execution) with
  | (Continue(id), Execution_completed(state, _)) when id = request_id ->
      state
  | (Continue(id), Execution_interrupted(state)) when id = request_id ->
      state
  | (Cancel(id), _) when
      id = request_id && not (command_is_interruptible command) ->
      failwith "uninterruptible request was cancelled"
  | (Cancel(id), Execution_completed(_, result)) when id = request_id ->
      finish_cancel_signal request_id;
      cleanup_completed command result;
      let state = rollback initial_state in
      let sid = Stateid.to_int state.Vernac.State.sid in
      send_control_ack (Cancel_ack {request_id; sid});
      state
  | (Cancel(id), Execution_interrupted(state)) when id = request_id ->
      finish_cancel_signal request_id;
      let sid = Stateid.to_int state.Vernac.State.sid in
      send_control_ack (Cancel_ack {request_id; sid});
      state
  | _ -> failwith "mismatched toplevel control decision"

let rec interact : state -> unit = fun state ->
  let pid = Unix.getpid () in
  Marshal.to_channel stdout (pid, Stateid.to_int state.Vernac.State.sid) [];
  Out_channel.flush stdout;
  let rec loop state =
    let request = Marshal.from_channel stdin in
    let state = run_request state request in
    loop state
  in
  try loop state with
  | Fork_child(state) -> interact state
  | End_of_file -> ()
  | Sys_error(s) -> Printf.eprintf "Error: %s.\n%!" s; exit 1

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

let parse_extra opts extras =
  let (async_opts, extras) = Stmargs.parse_args opts extras in
  ((), async_opts), extras

let run ((), async_opts) ~opts injections =
  Feed.with_feeder @@ fun _ ->
  let state = init_toploop opts async_opts injections in
  Feed.reset ();
  Flags.without_option Flags.in_ml_toplevel interact state

let _ =
  let args = List.tl (Array.to_list Sys.argv) in
  let usage =
    let executable_name = "rocq_simple_repl" in
    Boot.Usage.{executable_name; extra_args = ""; extra_options = ""}
  in
  let coqtop_toplevel =
    let initial_args = Coqargs.default in
    let init_extra _ injections ~opts:_ = injections in
    Coqtop.{parse_extra; usage; init_extra; run; initial_args}
  in
  Coqtop.start_coq coqtop_toplevel args

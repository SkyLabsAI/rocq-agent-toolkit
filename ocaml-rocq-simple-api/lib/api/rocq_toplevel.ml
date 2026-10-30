include Binaries_ready
include Rocq_simple_api_internal.Rocq_toplevel_data

type stopped_reason =
  | Normal
  | Killed
  | Failed of exn

type interrupted_reason =
  | Interrupt
  | Killed
  | Failed of exn

type state =
  | Idle
  | Reserving of {interruptible : bool; cancel_pending : bool}
  | Preparing of {
      request_id : int;
      interruptible : bool;
      cancel_pending : bool;
    }
  | Running of {request_id : int; interruptible : bool}
  | Completing of {request_id : int}
  | Cancelling of {request_id : int}
  | Interrupting of {request_id : int}
  | Stopping
  | Killing
  | Failing of {error : exn}
  | Terminated of {reason : stopped_reason}

type toplevel = {
  uid : int;
  oc : Out_channel.t;
  ic : In_channel.t;
  pid : int;
  direct_child : bool;
  supervisor : Out_channel.t option;
  state : state Atomic.t;
  closed : bool Atomic.t;
  next_request_id : int Atomic.t;
  mutable sid : int;
}

let next_toplevel_uid : unit -> int =
  let uid = Atomic.make (-1) in
  fun () -> Atomic.fetch_and_add uid 1 + 1

let close_fd_noerr fd =
  try Unix.close fd with Unix.Unix_error(_,_,_) -> ()

let with_sigpipe_blocked f =
  let was_pending = List.mem Sys.sigpipe (Unix.sigpending ()) in
  let previous_mask = Unix.sigprocmask SIG_BLOCK [Sys.sigpipe] in
  let restore_mask () =
    if not was_pending && List.mem Sys.sigpipe (Unix.sigpending ()) then
      ignore (Unix.sigwait [Sys.sigpipe]);
    ignore (Unix.sigprocmask SIG_SETMASK previous_mask)
  in
  Fun.protect ~finally:restore_mask f

let send_marshaled oc value =
  with_sigpipe_blocked @@ fun () ->
  Marshal.to_channel oc value [];
  Out_channel.flush oc

let close_out_noerr oc =
  try with_sigpipe_blocked (fun () -> Out_channel.close oc) with _ -> ()

let close_fd_ref_noerr owned_fd =
  match !owned_fd with
  | None -> ()
  | Some(fd) -> owned_fd := None; close_fd_noerr fd

let unlink file =
  try Unix.unlink file with Unix.Unix_error(_,_,_) -> ()

let rmdir dir =
  try Unix.rmdir dir with Unix.Unix_error(_,_,_) -> ()

let rec waitpid pid =
  try snd (Unix.waitpid [] pid) with
  | Unix.Unix_error(EINTR, _, _) -> waitpid pid

let status_explanation = function
  | Unix.WEXITED(i)   -> Printf.sprintf "exited with code %i" i
  | Unix.WSIGNALED(i) -> Printf.sprintf "killed with signal %i" i
  | Unix.WSTOPPED(i)  -> Printf.sprintf "stopped by signal %i" i

let kill_pid pid signal =
  try Unix.kill pid signal with Unix.Unix_error(_,_,_) -> ()

let kill_group pid signal =
  try Unix.kill (-pid) signal with Unix.Unix_error(_,_,_) -> ()

let kill_process pid signal =
  kill_group pid signal;
  kill_pid pid signal

let make_toplevel ~uid ~oc ~ic ~pid ~direct_child ~supervisor ~sid =
  let state = Atomic.make Idle in
  let closed = Atomic.make false in
  let next_request_id = Atomic.make 0 in
  {uid; oc; ic; pid; direct_child; supervisor; state; closed;
    next_request_id; sid}

exception Stopped of stopped_reason
exception Interrupted of interrupted_reason
exception Busy

let send_supervisor_control_noerr oc control =
  try send_marshaled oc control with _ -> ()

let cleanup ?(kill=false) (t : toplevel) =
  if Atomic.compare_and_set t.closed false true then begin
    begin match (kill, t.supervisor) with
    | (true, None) -> kill_process t.pid Sys.sigkill
    | (true, Some(oc)) ->
        send_supervisor_control_noerr oc Supervisor_kill
    | (false, _) -> ()
    end;
    close_out_noerr t.oc;
    In_channel.close_noerr t.ic;
    begin match (kill, t.supervisor) with
    | (false, Some(oc)) ->
        send_supervisor_control_noerr oc Supervisor_stop
    | _ -> ()
    end;
    Option.iter close_out_noerr t.supervisor;
    if t.direct_child then
      try ignore (waitpid t.pid) with Unix.Unix_error(_, _, _) -> ()
  end

let pause () = Unix.sleepf 0.0001

let raise_stopped (reason : stopped_reason) =
  raise (Stopped reason)

let raise_interrupted (reason : interrupted_reason) =
  raise (Interrupted reason)

let rec mark_failed t error =
  let state = Atomic.get t.state in
  match state with
  | Cancelling _ -> pause (); mark_failed t error
  | Stopping | Killing | Failing _ | Terminated _ -> ()
  | _ ->
      let failing = Failing {error} in
      if Atomic.compare_and_set t.state state failing then begin
        cleanup ~kill:true t;
        Atomic.set t.state (Terminated {reason = Failed error})
      end else
        mark_failed t error

let init : args:string list -> toplevel = fun ~args ->
  let prog = "rocq-simple-api.private.toplevel" in
  let argv = Array.of_list (prog :: args) in
  let (command_in, command_out) = Unix.pipe ~cloexec:true () in
  let (response_in, response_out) =
    try Unix.pipe ~cloexec:true () with e ->
      close_fd_noerr command_in;
      close_fd_noerr command_out;
      raise e
  in
  let command_in = ref (Some(command_in)) in
  let command_out = ref (Some(command_out)) in
  let response_in = ref (Some(response_in)) in
  let response_out = ref (Some(response_out)) in
  let pid = ref None in
  let ic = ref None in
  let oc = ref None in
  let cleanup_startup () =
    close_fd_ref_noerr command_in;
    close_fd_ref_noerr command_out;
    close_fd_ref_noerr response_in;
    close_fd_ref_noerr response_out;
    Option.iter In_channel.close_noerr !ic;
    Option.iter close_out_noerr !oc;
    ic := None;
    oc := None
  in
  let take_fd owned_fd =
    match !owned_fd with
    | None -> assert false
    | Some(fd) -> owned_fd := None; fd
  in
  try
    let child =
      Unix.create_process_env prog argv (Unix.environment ())
        (Option.get !command_in) (Option.get !response_out) Unix.stderr
    in
    pid := Some(child);
    close_fd_ref_noerr command_in;
    close_fd_ref_noerr response_out;
    let command_fd = take_fd command_out in
    let command_oc =
      try Unix.out_channel_of_descr command_fd with e ->
        close_fd_noerr command_fd;
        raise e
    in
    oc := Some(command_oc);
    let response_fd = take_fd response_in in
    let response_ic =
      try Unix.in_channel_of_descr response_fd with e ->
        close_fd_noerr response_fd;
        raise e
    in
    ic := Some(response_ic);
    set_binary_mode_out command_oc true;
    set_binary_mode_in response_ic true;
    let (reported_pid, sid) =
      try Marshal.from_channel response_ic with End_of_file ->
      let explanation = status_explanation (waitpid child) in
      pid := None;
      raise (Failure("the toplevel process failed to start (" ^
        explanation ^ ")"))
    in
    if reported_pid <> child then begin
      kill_process child Sys.sigkill;
      ignore (waitpid child);
      pid := None;
      failwith "the toplevel process reported an unexpected PID"
    end;
    let top =
      make_toplevel ~uid:(next_toplevel_uid ()) ~oc:command_oc ~ic:response_ic
        ~pid:child ~direct_child:true ~supervisor:None ~sid
    in
    oc := None;
    ic := None;
    top
  with e ->
    Option.iter (fun child -> kill_process child Sys.sigkill) !pid;
    Option.iter (fun child -> try ignore (waitpid child) with _ -> ()) !pid;
    cleanup_startup ();
    raise e

let rec stop t =
  let state = Atomic.get t.state in
  match state with
  | Stopping | Killing | Failing _ -> pause (); stop t
  | Terminated {reason} -> raise_stopped reason
  | Idle ->
      if Atomic.compare_and_set t.state state Stopping then begin
        cleanup t;
        Atomic.set t.state (Terminated {reason = Normal})
      end else
        stop t
  | Reserving _ | Preparing _ | Running _ | Completing _ | Cancelling _
  | Interrupting _ -> raise Busy

let send_control t control =
  send_marshaled t.oc control

let publish_cancellation t state request_id =
  try
    send_control t (Cancel request_id);
    kill_group t.pid Sys.sigint;
    send_control t (Cancel_signal_sent request_id);
    let interrupting = Interrupting {request_id} in
    if not (Atomic.compare_and_set t.state state interrupting) then
      failwith "invalid toplevel state after cancellation publication";
    Ok(())
  with error ->
    let failing = Failing {error} in
    if Atomic.compare_and_set t.state state failing then begin
      cleanup ~kill:true t;
      Atomic.set t.state (Terminated {reason = Failed error});
      Error(error)
    end else
      failwith "invalid toplevel state after cancellation failure"

let rec interrupt t =
  let state = Atomic.get t.state in
  match state with
  | Idle | Completing _ -> ()
  | Stopping | Killing | Failing _ -> pause (); interrupt t
  | Terminated {reason} -> raise_stopped reason
  | Reserving {interruptible = false; _}
  | Preparing {interruptible = false; _}
  | Running {interruptible = false; _} -> ()
  | Reserving {interruptible = true; cancel_pending = false} ->
      let pending = Reserving {interruptible = true; cancel_pending = true} in
      if not (Atomic.compare_and_set t.state state pending) then
        interrupt t
  | Preparing {
      request_id; interruptible = true; cancel_pending = false;
    } ->
      let pending = Preparing {
        request_id; interruptible = true; cancel_pending = true;
      } in
      if not (Atomic.compare_and_set t.state state pending) then
        interrupt t
  | Reserving {interruptible = true; cancel_pending = true}
  | Preparing {interruptible = true; cancel_pending = true; _}
  | Cancelling _ | Interrupting _ -> ()
  | Running {request_id; interruptible = true} ->
      let cancelling = Cancelling {request_id} in
      if Atomic.compare_and_set t.state state cancelling then begin
        match publish_cancellation t cancelling request_id with
        | Ok(()) -> ()
        | Error(error) -> raise_stopped (Failed error)
      end else
        interrupt t

let rec kill t =
  let state = Atomic.get t.state in
  match state with
  | Cancelling _ | Stopping | Killing | Failing _ -> pause (); kill t
  | Terminated {reason} -> raise_stopped reason
  | Idle | Reserving _ | Preparing _ | Running _ | Completing _
  | Interrupting _ ->
      if Atomic.compare_and_set t.state state Killing then begin
        cleanup ~kill:true t;
        Atomic.set t.state (Terminated {reason = Killed})
      end else
        kill t

let get_pid : toplevel -> int = fun t ->
  match Atomic.get t.state with
  | Stopping -> raise_stopped Normal
  | Killing -> raise_stopped Killed
  | Failing {error} -> raise_stopped (Failed error)
  | Terminated {reason} -> raise_stopped reason
  | Idle | Reserving _ | Preparing _ | Running _ | Completing _
  | Cancelling _ | Interrupting _ -> t.pid

exception Toplevel_mismatch

module StateID = struct
  type t = {toplevel : int; sid : int}

  let current : toplevel -> t = fun t ->
    match Atomic.get t.state with
    | Stopping -> raise_stopped Normal
    | Killing -> raise_stopped Killed
    | Failing {error} -> raise_stopped (Failed error)
    | Terminated {reason} -> raise_stopped reason
    | Idle -> {toplevel = t.uid; sid = t.sid}
    | Reserving _ | Preparing _ | Running _ | Completing _ | Cancelling _
    | Interrupting _ -> raise Busy

  let to_int : toplevel -> t -> int = fun t {toplevel; sid} ->
    if toplevel <> t.uid then raise Toplevel_mismatch else sid

  let unsafe_of_int : toplevel -> int -> t = fun t sid ->
    {toplevel = t.uid; sid}
end

let begin_request t ~interruptible =
  let rec publish_request_id request_id =
    let state = Atomic.get t.state in
    match state with
    | Reserving {interruptible; cancel_pending} ->
        let preparing =
          Preparing {request_id; interruptible; cancel_pending}
        in
        if Atomic.compare_and_set t.state state preparing then
          request_id
        else
          publish_request_id request_id
    | Killing | Failing _ -> pause (); publish_request_id request_id
    | Terminated {reason = Normal} -> raise_stopped Normal
    | Terminated {reason = Killed} -> raise_interrupted Killed
    | Terminated {reason = Failed error} ->
        raise_interrupted (Failed error)
    | _ -> failwith "invalid toplevel state while reserving a request"
  in
  let rec acquire () =
    let state = Atomic.get t.state in
    match state with
    | Idle ->
        let reserving = Reserving {interruptible; cancel_pending = false} in
        if Atomic.compare_and_set t.state state reserving then begin
          let request_id = Atomic.fetch_and_add t.next_request_id 1 in
          publish_request_id request_id
        end else
          acquire ()
    | Stopping -> raise_stopped Normal
    | Killing | Failing _ -> pause (); acquire ()
    | Terminated {reason} -> raise_stopped reason
    | Reserving _ | Preparing _ | Running _ | Completing _ | Cancelling _
    | Interrupting _ -> raise Busy
  in
  acquire ()

let activate_request t request_id =
  let rec loop () =
    let state = Atomic.get t.state in
    match state with
    | Preparing {
        request_id = id; interruptible; cancel_pending = false;
      } when id = request_id ->
        let running = Running {request_id; interruptible} in
        if not (Atomic.compare_and_set t.state state running) then
          loop ()
    | Preparing {
        request_id = id; interruptible = true; cancel_pending = true;
      } when id = request_id ->
        let cancelling = Cancelling {request_id} in
        if Atomic.compare_and_set t.state state cancelling then begin
          match publish_cancellation t cancelling request_id with
          | Ok(()) -> ()
          | Error(error) -> raise_interrupted (Failed error)
        end else
          loop ()
    | Killing | Failing _ -> pause (); loop ()
    | Stopping -> raise_stopped Normal
    | Terminated {reason = Normal} -> raise_stopped Normal
    | Terminated {reason = Killed} -> raise_interrupted Killed
    | Terminated {reason = Failed error} ->
        raise_interrupted (Failed error)
    | _ -> failwith "invalid toplevel state after Started"
  in
  loop ()

let finish_completed t request_id sid =
  let rec loop () =
    let state = Atomic.get t.state in
    match state with
    | Running {request_id = id; _} when id = request_id ->
        let completing = Completing {request_id} in
        if Atomic.compare_and_set t.state state completing then begin
          send_control t (Continue request_id);
          t.sid <- sid;
          if not (Atomic.compare_and_set t.state completing Idle) then begin
            match Atomic.get t.state with
            | Killing -> raise_interrupted Killed
            | Failing {error} -> raise_interrupted (Failed error)
            | Stopping -> raise_stopped Normal
            | Terminated {reason = Normal} -> raise_stopped Normal
            | Terminated {reason = Killed} -> raise_interrupted Killed
            | Terminated {reason = Failed error} ->
                raise_interrupted (Failed error)
            | _ -> failwith "invalid toplevel state after completion"
          end
        end else
          loop ()
    | Cancelling {request_id = id} when id = request_id ->
        pause ();
        loop ()
    | Interrupting {request_id = id} when id = request_id ->
        let ack = (Marshal.from_channel t.ic : control_ack) in
        let ack_sid =
          match ack with
          | Cancel_ack {request_id = id; sid} when id = request_id -> sid
          | _ -> failwith "mismatched cancellation acknowledgement"
        in
        t.sid <- ack_sid;
        if Atomic.compare_and_set t.state state Idle then
          raise_interrupted Interrupt;
        begin match Atomic.get t.state with
        | Killing | Failing _ -> pause (); loop ()
        | Stopping -> raise_stopped Normal
        | Terminated {reason = Normal} -> raise_stopped Normal
        | Terminated {reason = Killed} -> raise_interrupted Killed
        | Terminated {reason = Failed error} ->
            raise_interrupted (Failed error)
        | _ -> failwith "invalid toplevel state after interruption"
        end
    | Killing | Failing _ -> pause (); loop ()
    | Stopping -> raise_stopped Normal
    | Terminated {reason = Normal} -> raise_stopped Normal
    | Terminated {reason = Killed} -> raise_interrupted Killed
    | Terminated {reason = Failed error} ->
        raise_interrupted (Failed error)
    | _ -> failwith "mismatched toplevel response"
  in
  loop ()

let rec fail_request t error =
  match Atomic.get t.state with
  | Killing -> pause (); fail_request t error
  | Failing _ -> pause (); fail_request t error
  | Stopping -> raise_stopped Normal
  | Terminated {reason = Killed} -> raise_interrupted Killed
  | Terminated {reason = Failed failure} ->
      raise_interrupted (Failed failure)
  | Terminated {reason = Normal} -> raise_stopped Normal
  | Idle | Reserving _ | Preparing _ | Running _ | Completing _
  | Cancelling _ | Interrupting _ ->
      mark_failed t error;
      fail_request t error

let request : type r e. toplevel -> (r, e) cmd -> (r, e) Result.t = fun t c ->
  let interruptible = command_is_interruptible c in
  let request_id = begin_request t ~interruptible in
  try
    let request = {request_id; command = c} in
    send_marshaled t.oc request;
    begin match (Marshal.from_channel t.ic : (r, e) message) with
    | Started(id) when id = request_id -> ()
    | Started(_) | Finished(_) ->
        failwith "mismatched toplevel start response"
    end;
    activate_request t request_id;
    let response =
      match (Marshal.from_channel t.ic : (r, e) message) with
      | Finished(response) -> response
      | Started(_) -> failwith "duplicate toplevel start response"
    in
    let (sid, result) =
      match response with
      | Completed({request_id = id; sid; result}) when id = request_id ->
          (sid, Some(result))
      | Interrupted({request_id = id; sid}) when id = request_id ->
          (sid, None)
      | Completed(_) | Interrupted(_) ->
          failwith "mismatched toplevel terminal response"
    in
    finish_completed t request_id sid;
    match result with
    | Some(result) -> result
    | None -> raise_interrupted Interrupt
  with
  | Interrupted _ | Stopped _ as e -> raise e
  | e -> fail_request t e

let back_to : toplevel -> sid:StateID.t -> (unit, string) result =
    fun t ~sid ->
  request t (BackTo({sid = StateID.to_int t sid}))

let start_loc loc =
  Loc.create loc.Loc.fname loc.line_nb loc.bol_pos loc.bp loc.bp

let run : toplevel -> loc:Loc.t -> text:string ->
    (run_data, string * run_error) result = fun t ~loc ~text ->
  request t (Run({loc = start_loc loc; text}))

let loc_after_blanks : toplevel -> loc:Loc.t -> text:string ->
    (Loc.t, string) result = fun t ~loc ~text ->
  request t (LocAfterBlanks({loc = start_loc loc; text}))

let structured_goals : toplevel -> structured_goal list option = fun t ->
  match request t StructuredGoals with Ok(goals) -> goals

let fork : toplevel -> (toplevel, string) result = fun t ->
  let dir = Filename.temp_dir "rocq_toplevel" "" in
  let pipe_in = Filename.concat dir "in" in
  let pipe_out = Filename.concat dir "out" in
  let pipe_supervisor = Filename.concat dir "supervisor" in
  let guard_in = ref None in
  let guard_out = ref None in
  let guard_supervisor = ref None in
  let child_ic = ref None in
  let child_oc = ref None in
  let supervisor_oc = ref None in
  let cleanup_files () =
    unlink pipe_in;
    unlink pipe_out;
    unlink pipe_supervisor;
    rmdir dir
  in
  let cleanup_guards () =
    Option.iter close_fd_noerr !guard_in;
    Option.iter close_fd_noerr !guard_out;
    Option.iter close_fd_noerr !guard_supervisor;
    guard_in := None;
    guard_out := None;
    guard_supervisor := None
  in
  let cleanup_channels () =
    Option.iter In_channel.close_noerr !child_ic;
    Option.iter close_out_noerr !child_oc;
    Option.iter close_out_noerr !supervisor_oc
  in
  let cleanup_temporary () =
    cleanup_channels ();
    cleanup_guards ();
    cleanup_files ()
  in
  let open_guard path =
    Unix.openfile path [O_RDWR; O_CLOEXEC] 0
  in
  begin try
    Unix.mkfifo pipe_in 0o600;
    Unix.mkfifo pipe_out 0o600;
    Unix.mkfifo pipe_supervisor 0o600;
    guard_in := Some(open_guard pipe_in);
    guard_out := Some(open_guard pipe_out);
    guard_supervisor := Some(open_guard pipe_supervisor);
    supervisor_oc := Some(Out_channel.open_bin pipe_supervisor)
  with e ->
    cleanup_temporary ();
    raise e
  end;
  let result =
    try request t (Fork {pipe_in; pipe_out; pipe_supervisor}) with
    | e -> cleanup_temporary (); raise e
  in
  match result with
  | Error(s) -> cleanup_temporary (); Error(s)
  | Ok(pid) ->
      try
        let oc = Out_channel.open_bin pipe_in in
        child_oc := Some(oc);
        let ic = In_channel.open_bin pipe_out in
        child_ic := Some(ic);
        let fd = Unix.descr_of_in_channel ic in
        begin match Unix.select [fd] [] [] 10. with
        | ([], _, _) -> failwith "the forked toplevel failed to start"
        | (_ :: _, _, _) -> ()
        end;
        cleanup_guards ();
        cleanup_files ();
        let (reported_pid, sid) = Marshal.from_channel ic in
        if reported_pid <> pid then
          failwith "the forked toplevel reported an unexpected PID";
        let supervisor = Option.get !supervisor_oc in
        supervisor_oc := None;
        Ok(make_toplevel ~uid:t.uid ~oc ~ic ~pid ~direct_child:false
          ~supervisor:(Some(supervisor)) ~sid)
      with
      | Sys_error(s) | Failure(s) ->
          Option.iter (fun oc ->
            send_supervisor_control_noerr oc Supervisor_kill
          ) !supervisor_oc;
          cleanup_temporary ();
          Error(s)
      | e ->
          Option.iter (fun oc ->
            send_supervisor_control_noerr oc Supervisor_kill
          ) !supervisor_oc;
          cleanup_temporary ();
          raise e

let get_items ~loc ~text ~complete commands =
  let off = loc.Loc.bp in
  let len = String.length text in
  let end_off = off + len in
  let cur_off = ref off in
  let rev_items = ref [] in
  let add kind bp ep =
    let rel_bp = bp - off in
    let rel_ep = ep - off in
    if rel_bp < 0 || rel_ep < rel_bp || len < rel_ep then assert false;
    let text = String.sub text rel_bp (rel_ep - rel_bp) in
    rev_items := {kind; text; bp; ep} :: !rev_items
  in
  let add_blanks ep =
    if ep < !cur_off then assert false;
    if !cur_off < ep then add `Blanks !cur_off ep;
    cur_off := ep
  in
  let add_command command =
    let loc = Option.get command.CAst.loc in
    add_blanks loc.Loc.bp;
    add (`Command(command)) loc.bp loc.ep;
    cur_off := loc.ep
  in
  List.iter add_command commands;
  if complete then add_blanks end_off else begin
    let offset = !cur_off - off in
    let blanks = Rocq_blanks.parse text ~offset in
    add_blanks (off + blanks.valid_until)
  end;
  (List.rev !rev_items, !cur_off - off)

let split : ?sid:StateID.t -> toplevel -> loc:Loc.t -> text:string ->
    (split_data, split_error) result = fun ?sid t ~loc ~text ->
  let sid = Option.map (StateID.to_int t) sid in
  let loc = start_loc loc in
  let raw = match request t (Split({sid; loc; text})) with Ok(raw) -> raw in
  match raw.result with
  | Ok(()) ->
      let (items, _) = get_items ~loc ~text ~complete:true raw.commands in
      Ok({items})
  | Error(error_text, error_loc) ->
      let (parsed_items, parsed_len) =
        get_items ~loc ~text ~complete:false raw.commands
      in
      let leftover_len = String.length text - parsed_len in
      let leftover = String.sub text parsed_len leftover_len in
      Error({parsed_items; leftover; error_text; error_loc})

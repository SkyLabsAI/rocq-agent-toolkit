include Binaries_ready
include Rocq_simple_api_internal.Rocq_toplevel_data

type toplevel = {
  uid : int;
  oc : Out_channel.t;
  ic : In_channel.t;
  pid : int;
  is_fork : bool;
  mutable stopped : bool;
  mutable sid : int;
}

let next_toplevel_uid : unit -> int =
  let uid = ref (-1) in
  let toplevel_uid _ = incr uid; !uid in
  toplevel_uid

let init : args:string list -> toplevel = fun ~args ->
  let prog = "rocq-simple-api.private.toplevel" in
  let argv = Array.of_list (prog :: args) in
  let (ic, oc) = Unix.open_process_args prog argv in
  let (pid, sid) =
    try Marshal.from_channel ic with End_of_file ->
    let explanation =
      match Unix.close_process (ic, oc) with
      | Unix.WEXITED(0)   -> assert false
      | Unix.WEXITED(i)   -> Printf.sprintf "exited with code %i" i
      | Unix.WSIGNALED(i) -> Printf.sprintf "killed with signal %i" i
      | Unix.WSTOPPED(i)  -> Printf.sprintf "stopped by signal %i" i
    in
    failwith ("the toplevel process failed to start (" ^ explanation ^ ")")
  in
  let uid = next_toplevel_uid () in
  {uid; oc; ic; pid; is_fork = false; stopped = false; sid}

exception Stopped

let check_not_stopped s =
  if s.stopped then raise Stopped

let kill pid =
  try Unix.kill pid Sys.sigkill with Unix.Unix_error(_,_,_) -> ()

let stop : toplevel -> unit = fun t ->
  check_not_stopped t;
  t.stopped <- true;
  match t.is_fork with
  | false -> ignore (Unix.close_process (t.ic, t.oc))
  | true  ->
      kill t.pid; In_channel.close_noerr t.ic; Out_channel.close_noerr t.oc

let get_pid : toplevel -> int = fun t ->
  check_not_stopped t; t.pid

exception Toplevel_mismatch

module StateID = struct
  type t = {toplevel : int; sid : int}

  let current : toplevel -> t = fun t ->
    {toplevel = t.uid; sid = t.sid}

  let to_int : toplevel -> t -> int = fun t {toplevel; sid} ->
    if toplevel <> t.uid then raise Toplevel_mismatch else sid

  let unsafe_of_int : toplevel -> int -> t = fun t sid ->
    {toplevel = t.uid; sid}
end

let request : type r e. toplevel -> (r, e) cmd -> (r, e) Result.t = fun s c ->
  check_not_stopped s;
  Marshal.to_channel s.oc c [];
  Out_channel.flush s.oc;
  let (sid, result) = Marshal.from_channel s.ic in
  s.sid <- sid; result

let back_to : toplevel -> sid:StateID.t -> (unit, string) result =
    fun s ~sid ->
  request s (BackTo({sid = StateID.to_int s sid}))

let run : toplevel -> off:int -> text:string ->
    (run_data, string * run_error) result = fun s ~off ~text ->
  request s (Run({off; text}))

let structured_goals : toplevel -> structured_goal list option = fun s ->
  match request s StructuredGoals with Ok(goals) -> goals

let unlink file =
  try Unix.unlink file with Unix.Unix_error(_,_,_) -> ()

let fork : toplevel -> (toplevel, string) result = fun s ->
  let base = Filename.temp_file "rocq_toplevel" "" in
  let pipe_in = base ^ ".in" in
  let pipe_out = base ^ ".out" in
  let cleanup_files () = unlink base; unlink pipe_in; unlink pipe_out in
  Unix.mkfifo pipe_in 0o600;
  Unix.mkfifo pipe_out 0o600;
  match request s (Fork({pipe_in; pipe_out})) with
  | Error(s) -> unlink base; unlink pipe_in; unlink pipe_out; Error(s)
  | Ok(pid)  ->
  match Out_channel.open_bin pipe_in with
  | exception Sys_error(s) ->
      kill pid; cleanup_files (); Error(s)
  | oc                     ->
  match In_channel.open_bin pipe_out with
  | exception Sys_error(s) ->
      kill pid; cleanup_files (); Out_channel.close_noerr oc; Error(s)
  | ic                     ->
  cleanup_files ();
  match snd (Marshal.from_channel ic) with
  | Ok(_)    -> Ok({s with oc; ic; pid; is_fork = true})
  | Error(s) ->
      Out_channel.close_noerr oc;
      In_channel.close_noerr ic;
      Error(s)

let get_items ~off ~text ~complete commands =
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

let split : ?sid:StateID.t -> toplevel -> off:int -> text:string ->
    (split_data, split_error) result = fun ?sid s ~off ~text ->
  let sid = Option.map (StateID.to_int s) sid in
  let raw = match request s (Split({sid; off; text})) with Ok(raw) -> raw in
  match raw.result with
  | Ok(()) ->
      let (items, _) = get_items ~off ~text ~complete:true raw.commands in
      Ok({items})
  | Error(error_text, error_loc) ->
      let (parsed_items, parsed_len) =
        get_items ~off ~text ~complete:false raw.commands
      in
      let leftover_len = String.length text - parsed_len in
      let leftover = String.sub text parsed_len leftover_len in
      Error({parsed_items; leftover; error_text; error_loc})

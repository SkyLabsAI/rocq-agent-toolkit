include Rocq_toplevel_data

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
  let prog = "rocq-toplevel-api.private" in
  let argv = Array.of_list (prog :: args) in
  let (ic, oc) = Unix.open_process_args prog argv in
  let uid = next_toplevel_uid () in
  let (pid, sid) = Marshal.from_channel ic in
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

let request : type r e. toplevel -> (r, e) command -> (r, e) Result.t =
    fun s c ->
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

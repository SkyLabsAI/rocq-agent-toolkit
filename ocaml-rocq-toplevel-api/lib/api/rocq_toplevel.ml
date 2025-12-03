include Rocq_toplevel_data

type toplevel = {
  uid : int;
  oc : Out_channel.t;
  ic : In_channel.t;
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
  let sid = Marshal.from_channel ic in
  {uid; oc; ic; stopped = false; sid}

exception Stopped

let check_not_stopped s =
  if s.stopped then raise Stopped

let stop : toplevel -> unit = fun t ->
  check_not_stopped t;
  t.stopped <- true;
  ignore (Unix.close_process (t.ic, t.oc))

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

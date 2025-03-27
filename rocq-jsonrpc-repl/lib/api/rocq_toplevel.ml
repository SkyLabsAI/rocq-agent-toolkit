type ('a, 'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

let panic : ('a, 'b) koutfmt -> 'a = fun fmt ->
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter
    ("Error: " ^^ fmt ^^ "\n%!")

let next_toplevel_uid : unit -> int =
  let uid = ref (-1) in
  let toplevel_uid _ = incr uid; !uid in
  toplevel_uid

module StateId = struct
  type t = {toplevel : int; id : int}
  [@@deriving yojson]

  let to_json = to_yojson

  let of_json json =
    match of_yojson json with
    | Ok(sid)  -> sid
    | Error(_) -> panic "not a valid state identifier"
end

type json = Yojson.Safe.t

type t = {
  uid              : int;
  oc               : Out_channel.t;
  ic               : In_channel.t;
  mutable last_id  : int;
  mutable stopped  : bool;
  mutable sid      : int;
  mutable feedback : json list option;
}

exception Stopped

let check_not_stopped t =
  if t.stopped then raise Stopped

let get_state_id t =
  check_not_stopped t;
  StateId.{toplevel = t.uid; id = t.sid}

let prog = "rocq-jsonrpc-repl"

let init : args:string list -> file:string -> t = fun ~args ~file ->
  let argv = Array.of_list (prog :: args @ ["-topfile"; file]) in
  let (ic, oc) = Unix.open_process_args prog argv in
  let uid = next_toplevel_uid () in
  {uid; oc; ic; last_id = 0; stopped = false; sid = 1; feedback = None}

let next_request_id : t -> Jsonrpc.Id.t = fun t ->
  t.last_id <- t.last_id + 1; `Int(t.last_id)

(* Always called after [check_not_stopped]. *)
let request : t -> f:string -> params:json list -> json = fun t ~f ~params ->
  let params = match params with [] -> None | _ -> Some(`List(params)) in
  let id = next_request_id t in
  let r = Jsonrpc.Request.create ?params ~id ~method_:f () in
  Jsonrpc_tp.send ~oc:t.oc (Jsonrpc.Packet.Request(r));
  match Jsonrpc_tp.recv ~ic:t.ic () with
  | Error(s)    -> panic "ill-formed packet received (%s)" s
  | Ok(None)    -> panic "end of file while waiting for a response"
  | Ok(Some(p)) ->
  let Jsonrpc.Response.{id = response_id; result} =
    match p with
    | Jsonrpc.Packet.Response(r) -> r
    | _                          ->
        panic "expected response, got another packet type"
  in
  if not (Jsonrpc.Id.equal id response_id) then
    panic "received the wrong response (different id)";
  match result with
  | Error(_) -> panic "received an error response"
  | Ok(json) -> json

let stop : t -> unit = fun t ->
  check_not_stopped t;
  let json = request t ~f:"quit" ~params:[] in
  if json <> `Null then panic "unexpected response data";
  t.stopped <- true;
  match Unix.close_process (t.ic, t.oc) with
  | Unix.WEXITED(0)   -> ()
  | Unix.WEXITED(i)   -> panic "toplevel exited with code %i" i
  | Unix.WSIGNALED(i) -> panic "toplevel killed with signal %i" i
  | Unix.WSTOPPED(i)  -> panic "toplevel stopped with signal %i" i

type loc = Rocq_loc.t option

let loc_of_json json =
  match Rocq_loc.of_json json with
  | Ok(loc)  -> loc
  | Error(_) -> panic "ill-formed location"

type feedback = {
  kind : [`Debug | `Info | `Notice | `Warning | `Error];
  text : string;
  loc  : loc;
}

exception No_feedback

let feedback_of_json : json -> feedback = fun json ->
  let fields =
    match json with
    | `Assoc(fields) -> fields
    | _              -> panic "ill-typed feedback object"
  in
  let kind =
    match List.assoc_opt "kind" fields with
    | Some(`String("debug"  )) -> `Debug
    | Some(`String("info"   )) -> `Info
    | Some(`String("notice" )) -> `Notice
    | Some(`String("warning")) -> `Warning
    | Some(`String("error"  )) -> `Error
    | _                        -> panic "unexpected feedback kind"
  in
  let text =
    match List.assoc_opt "text" fields with
    | Some(`String(text)) -> text
    | Some(_            ) -> panic "ill-typed text field of feedback"
    | None                -> panic "missing text field in feedback"
  in
  let loc = Option.map loc_of_json (List.assoc_opt "loc" fields) in
  {kind; text; loc}

let get_feedback : t -> feedback list = fun t ->
  match t.feedback with
  | None           -> raise No_feedback
  | Some(feedback) -> List.map feedback_of_json feedback

exception Toplevel_mismatch

type resp =
  | Success of {payload : json option}
  | Failure of {loc : json option; error : string}

(* Always called after [check_not_stopped]. *)
let request : t -> f:string -> params:json list -> resp = fun t ~f ~params ->
  let json = request t ~f ~params in
  let fields =
    match json with `Assoc(fields) -> fields | _ ->
    panic "unexpected response payload"
  in
  let success =
    match List.assoc_opt "success" fields with
    | Some(`Bool(b)) -> b
    | Some(_       ) -> panic "ill-typed success field of response"
    | None           -> panic "missing success field in response"
  in
  let feedback =
    match List.assoc_opt "feedback" fields with
    | Some(`List(l)) -> l
    | Some(_       ) -> panic "ill-typed feedback field in response"
    | None           -> []
  in
  t.feedback <- Some(feedback);
  let build_success () =
    let new_sid =
      match List.assoc_opt "state" fields with
      | Some(`Int(i)) -> i
      | Some(_      ) -> panic "ill-typed state field in response"
      | None          -> panic "missing state field in response"
    in
    t.sid <- new_sid;
    let payload = List.assoc_opt "data" fields in
    Success({payload})
  in
  let build_failure () =
    let loc = List.assoc_opt "loc" fields in
    let error =
      match List.assoc_opt "error" fields with
      | Some(`String(s)) -> s
      | Some(_         ) -> panic "ill-typed error field in response"
      | None             -> panic "missing error field in response"
    in
    Failure({loc; error})
  in
  if success then build_success () else build_failure ()

let int_of_sid : t -> StateId.t -> int = fun t sid ->
  if sid.StateId.toplevel <> t.uid then raise Toplevel_mismatch;
  sid.StateId.id

let back_to : t -> sid:StateId.t -> (unit, string) result = fun t ~sid ->
  check_not_stopped t;
  let sid = int_of_sid t sid in
  match request t ~f:"back_to" ~params:[`Int(sid)] with
  | Failure({loc = _; error}) -> Error(error)
  | Success({payload = None}) -> Ok(())
  | Success({payload = _   }) -> panic "unexpected payload"

let show_goal : t -> sid:StateId.t -> gid:int -> (string, string) result =
    fun t ~sid ~gid ->
  check_not_stopped t;
  let sid = int_of_sid t sid in
  match request t ~f:"show_goal" ~params:[`Int(gid); `Int(sid)] with
  | Failure({loc = _; error})       -> Error(error)
  | Success({payload = None      }) -> panic "payload expected"
  | Success({payload = Some(json)}) ->
  match json with
  | `String(s) -> Ok(s)
  | _          -> panic "ill-typed payload"

let run : t -> off:int -> text:string ->
    (string option, loc * string) result = fun t ~off ~text ->
  check_not_stopped t;
  match request t ~f:"run" ~params:[`Int(off); `String(text)] with
  | Failure({loc; error})           ->
      let loc = Option.map loc_of_json loc in
      Error(loc, error)
  | Success({payload = None      }) -> Ok(None)
  | Success({payload = Some(json)}) ->
  match json with
  | `String(s) -> Ok(Some(s))
  | _          -> panic "ill-typed payload"

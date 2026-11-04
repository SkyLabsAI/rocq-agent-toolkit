open Stdlib_extra.Extra

type session_id = string

val init : Dune_util.config -> bool -> Filepath.t -> unit

type interrupt_result =
  | Interrupt_requested
  | No_active_request
  | No_active_operation

val interrupt : session_id -> kill:bool -> interrupt_result

val full_client_request : session_id -> ('a, 'b, 'c) Request.t
  -> 'a * ('b, string * 'c) Result.t

val client_request : session_id -> (unit, 'a, 'b) Request.t
  -> ('a, string * 'b) Result.t

val stop : session_id -> unit

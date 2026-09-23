open Stdlib_extra.Extra

val init : bool -> Dune_util.config -> Filepath.t -> unit

val full_client_request : Filepath.t -> ('a, 'b, 'c) Request.t
  -> 'a * ('b, string * 'c) Result.t

val client_request : Filepath.t -> (unit, 'a, 'b) Request.t
  -> ('a, string * 'b) Result.t

val stop : Filepath.t -> unit

open Stdlib_extra.Extra

type empty = |

type insert_keep = Atomic | SuccessfulPrefix | All

type insert_error = {
  remaining : string;
  unchanged : bool;
}

type (_, _, _) t =
  | Stop : (unit, unit, empty) t
  | Status : {context : int option} -> (unit, string, empty) t
  | Steps : {count : int option} -> (Document.commands_data, int, int) t
  | Insert : {text : string; keep : insert_keep}
      -> (Document.commands_data, unit, insert_error) t
  | Query : {text : string} -> (unit, string, unit) t
  | Delete : {count : int} -> (unit, unit, unit) t
  | Commit : {file : string option; exclude_suffix : bool}
      -> (unit, int, unit) t
  | Goals : (unit, string, empty) t
  | Backwards : {count : int} -> (unit, unit, unit) t
  | Goto : {line: int; col: int option} -> (unit, unit, int) t

val is_stop : ('a, 'b, 'c) t -> bool

val pp : ('a, 'b, 'c) t Format.pp

val run : Document.t -> ('a, 'b, 'c) t -> 'a * ('b, string * 'c) Result.t

val print_feedback : Document.commands_data -> unit

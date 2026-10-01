open Stdlib_extra.Extra

type empty = |

type insert_keep = [`Atomic | `Successful | `All | `None]

type context = No_context | All_context | Context_lines of int

type print_after = {
  context : context;
  goals : bool;
}

type insert_error = {
  remaining : string;
  unchanged : bool;
}

type position = int * int

type (_, _, _) t =
  | Stop : (unit, unit, empty) t
  | Status : {mode : [`JSON | `Text of print_after]}
      -> (unit, string, empty) t
  | Steps : {count : int option; print : print_after}
      -> (Document.commands_data * string, int, int) t
  | Insert : {text : string; keep : insert_keep; print : print_after}
      -> (Document.commands_data * string, unit, insert_error) t
  | Query : {text : string} -> (unit, string, unit) t
  | Delete : {count : int option; print : print_after}
      -> (string, unit, unit) t
  | Commit : {file : string option; force : bool; include_suffix : bool}
      -> (unit, unit, unit) t
  | Goals : (unit, string, empty) t
  | Backwards : {count : int option; print : print_after}
      -> (string, unit, unit) t
  | Goto : {line: int; col: int option; print : print_after}
      -> (string, unit, position option) t

val is_stop : ('a, 'b, 'c) t -> bool

val pp : ('a, 'b, 'c) t Format.pp

val run : Document.t -> ('a, 'b, 'c) t -> 'a * ('b, string * 'c) Result.t

val print_feedback : Document.commands_data -> unit

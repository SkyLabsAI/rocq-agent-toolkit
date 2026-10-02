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

type move_direction = Forward | Backward

type move_target =
  | Position of {line : int; col : int option}
  | Absolute of int
  | Relative of move_direction * int option

type move_error =
  | Relative_failure of int
  | Target_failure of position option

type (_, _, _) t =
  | Stop : (unit, unit, empty) t
  | Status : {mode : [`JSON | `Text of print_after]}
      -> (unit, string, empty) t
  | Move : {target : move_target; print : print_after}
      -> (Document.commands_data * string, int, move_error) t
  | Insert : {text : string; keep : insert_keep; print : print_after}
      -> (Document.commands_data * string, unit, insert_error) t
  | Delete : {count : int option; print : print_after}
      -> (string, unit, unit) t
  | Commit : {file : string option; force : bool; include_suffix : bool}
      -> (unit, unit, unit) t
  | Goals : (unit, string, empty) t

val is_stop : ('a, 'b, 'c) t -> bool

val pp : ('a, 'b, 'c) t Format.pp

val run : Document.t -> ('a, 'b, 'c) t -> 'a * ('b, string * 'c) Result.t

val print_feedback : Feedback.level list -> Document.commands_data -> unit

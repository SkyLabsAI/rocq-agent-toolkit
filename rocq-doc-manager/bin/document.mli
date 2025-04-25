type t

val init : args:string list -> file:string -> t

val stop : t -> unit

val load_file : t -> (unit, string) result

type loc = Rocq_loc.t option

val loc_to_json : loc -> Yojson.Safe.t

type command_data = {
  open_subgoals : string option;
  new_constants : string list;
  new_inductives : string list;
}

val command_data_to_json : command_data -> Yojson.Safe.t

val insert_blanks : t -> text:string -> unit

val insert_command : t -> text:string -> (command_data, loc * string) result

val revert_before : t -> index:int -> unit

val clear_suffix : t -> unit

val run_step : t -> (command_data option, loc * string) result

val doc_prefix : t -> (kind:string -> off:int -> text:string -> 'a) -> 'a list

val doc_suffix : t -> (kind:string -> text:string -> 'a) -> 'a list

val has_suffix : t -> bool

val commit : t -> include_suffix:bool -> unit

val compile : t -> (unit, string) result * string * string

type feedback = {
  kind : [`Debug | `Info | `Notice | `Warning | `Error];
  text : string;
  loc  : loc;
}

val feedback_to_json : feedback -> Yojson.Safe.t

val get_feedback : t -> feedback list

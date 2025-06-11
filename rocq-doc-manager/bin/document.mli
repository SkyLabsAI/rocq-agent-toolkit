type t

val init : args:string list -> file:string -> t

val stop : t -> unit

val load_file : t -> (unit, string) result

type loc = Rocq_loc.t option

val loc_to_json : loc -> Yojson.Safe.t

type command_data = {
  open_subgoals : string option;
  new_constants : string list;
  removed_constants : string list;
  new_inductives : string list;
  removed_inductives : string list;
}

val file : t -> string

val command_data_to_json : command_data -> Yojson.Safe.t

val insert_blanks : t -> text:string -> unit

val insert_command : t -> text:string -> (command_data, loc * string) result

val revert_before : t -> index:int -> unit

val clear_suffix : t -> unit

val run_step : t -> (command_data option, loc * string) result

type byte_loc = {off : int; len : int}

val byte_loc_of_last_step : t -> byte_loc option

type processed_item = {
  index : int;
  kind : [`Blanks | `Command];
  off : int;
  text : string;
}

val last_processed_item : t -> processed_item option

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

(** [query d ~text] runs the command [text] at the cursor in document [d]. The
    cursor is not moved, and the command is not recorded in the document. Note
    also that the Rocq state is rolled back, to undo any potential side-effect
    that the query would have normally performed. Note that the function gives
    a similar result to [insert_command]. However, feedback is always returned
    immediately in the success case, and no source code location is given when
    an error occurs (queries are not part of the document). *)
val query : t -> text:string -> (command_data * feedback list, string) result

(** [text_query d ~text] is similar to [query d ~text], but the command result
    is extracted from the feedback, and returned as a string upon success. For
    that reason, the command [text] is assumed to produce exactly one "notice"
    feedback item, and its contents is taken as the query's result. An [Error]
    is returned if no such item is found. *)
val text_query : t -> text:string -> (string, string) result

(** [json_query d ~text] is similar to [text_query d ~text], but the result is
    additionally turned into JSON data. If the command does not return a valid
    JSON string (through a "notice" feedback item), an [Error] is returned. *)
val json_query : t -> text:string -> (Yojson.Safe.t, string) result

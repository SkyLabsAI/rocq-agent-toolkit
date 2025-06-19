(** Rocq document API.

    A Rocq document can be understood as an in-memory Rocq source file. It may
    of may not correspond to an existing source file, and may or may not be in
    sync with such a source file when it exists.

    A document is represented as a list of items, which can be of two kinds: a
    Rocq command, or a sequence of blanks (i.e., insignificant characters like
    spaces, or comments). A document additionally has a cursor splitting items
    into the prefix of already processed items, and the suffix of what remains
    to be processed. Said otherwise, the cursor is the index of the first item
    of the document's suffix. *)

(** Imperative state for a Rocq document. *)
type t

(** [init ~args ~file] initialises a Rocq document for the given [file], using
    the given Rocq command line arguments [args]. Regardless of whether [file]
    exists on the file system or not, the document starts empty. *)
val init : args:string list -> file:string -> t

val stop : t -> unit

val load_file : t -> (unit, string) result

type loc = Rocq_loc.t option

type json = Yojson.Safe.t

val loc_to_json : loc -> json

type command_data = {
  open_subgoals : string option;
  new_constants : string list;
  removed_constants : string list;
  new_inductives : string list;
  removed_inductives : string list;
}

val file : t -> string

val command_data_to_json : command_data -> json

val insert_blanks : t -> text:string -> unit

val insert_command : t -> text:string -> (command_data, loc * string) result

(** [run_command d ~text] is similar to [insert_command d ~text], but does not
    record the run command in the document. Note however that any side-effects
    that the command may have on the Rocq state is preserved. Note that in the
    [Error] case, no location is provided. *)
val run_command : t -> text:string -> (command_data, string) result

(** [cursor_index d] returns the index currently at the cursor in the document
    [d]. Note that this corresponds to the index of the first unprocessed item
    (if any). *)
val cursor_index : t -> int

(** [revert_before ?erase d ~index] reverts the cursor of document [d] back to
    before the processed item at the given [index]. If [index] is invalid, the
    [Invalid_argument] exception is raised. The [erase] boolean (defaulting to
    [false]) indicates whether the reverted items must be erased or added back
    to the suffix of unprocessed commands. *)
val revert_before : ?erase:bool -> t -> index:int -> unit

(** [with_rollback d f] runs [f ()], and then rolls back the document state so
    that the effects of the call to [f] are reverted. Note that [f] should not
    raise exceptions. *)
val with_rollback : t -> (unit -> 'a) -> 'a

val clear_suffix : t -> unit

val run_step : t -> (command_data option, loc * string) result

(** [advance_to d ~index] advances the cursor of document [d] to place it just
    before the item with the given [index]. If [index] is invalid, which means
    that it does not point to a valid item index (or one past the index of the
    last item), or that it points to an already processed item, then exception
    [Invalid_argument] is raised. In case of error while processing a command,
    the cursor is left at the reached position, and [Error (loc,msg)] is given
    similarly to what [insert_command] or [run_step] do. *)
val advance_to : t -> index:int -> (unit, loc * string) result

(** [go_to d ~index] is the same as [advance_to d ~index], but it additionally
    allows to revert to an earlier index like [revert_before d ~index]. In any
    case, no item is erased from the document. If the [index] is invalid, then
    [Invalid_argument] is raised. Valid indices range from [0] to one past the
    index of the last item in the document's suffix. *)
val go_to : t -> index:int -> (unit, loc * string) result

type byte_loc = {off : int; len : int}

val byte_loc_of_last_step : t -> byte_loc option

type processed_item = {
  index : int;
  kind : [`Blanks | `Command];
  off : int;
  text : string;
}

val last_processed_item : t -> processed_item option

type unprocessed_item = {
  kind : [`Blanks | `Command];
  text : string;
}

val first_unprocessed_item : t -> unprocessed_item option

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

val feedback_to_json : feedback -> json

val get_feedback : t -> feedback list

(** [query d ~text] runs the command [text] at the cursor in document [d]. The
    cursor is not moved, and the command is not recorded in the document. Note
    also that the Rocq state is rolled back, to undo any potential side-effect
    that the query would have normally performed. Note that the function gives
    a similar result to [insert_command]. However, feedback is always returned
    immediately in the success case, and no source code location is given when
    an error occurs (queries are not part of the document). *)
val query : t -> text:string -> (command_data * feedback list, string) result

(** [text_query ?index d ~text] is similar to [query d ~text], but the command
    result is extracted from the feedback, and returned as a string in case of
    success. If [index] is not given, the command [text] is assumed to produce
    exactly one "info" or "notice" feedback item, and its contents is taken as
    result of the query. Otherwise, the [index] identifies the "info"/"notice"
    feedback item to use as result. An [Error] is given when no valid feedback
    item is found. *)
val text_query : ?index:int -> t -> text:string -> (string, string) result

(** [text_query_all ?indices d ~text] is like [text_query d ~text], but it can
    retrieve several "info"/"notice" feedback items at once. When [indices] is
    not given, then the list of all "info"/"notice" items is returned. When an
    [indices] value is given, then a list of same size containing the items at
    corresponding indices is returned. In the case where any of the indices is
    invalid, [Error] is returned. *)
val text_query_all : ?indices:int list -> t -> text:string
  -> (string list, string) result

(** [json_query ?index d ~text] is similar to [text_query ?index d ~text], but
    the result is additionally turned into JSON data. If the command result is
    not a valid JSON string, an [Error] is returned. *)
val json_query : ?index:int -> t -> text:string -> (json, string) result

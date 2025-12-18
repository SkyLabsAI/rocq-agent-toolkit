(** Rocq document API.

    A Rocq document can be understood as an in-memory Rocq source file. It may
    or may not correspond to an existing source file, and may or may not be in
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
    exists on the file system or not, the document starts empty. Upon document
    creation, a session with a dedicated Rocq top-level is started. *)
val init : args:string list -> file:string -> t

(** Exception raised when running any of the following operation on a document
    that is already stopped. *)
exception Stopped

(** [stop d] marks document [d] as stopped, and stops the underlying top-level
    if it is not still shared with other documents (see [clone]). Note that it
    is required to eventually call stop on all documents returned by [init] or
    [clone], in order to free the underlying resources. *)
val stop : t -> unit

(** [clone d] creates an independent clone of the document [d], that starts in
    the same state as [d]. While document [d] and the produced clone both have
    their own state, they share a single underlying Rocq top-level. This means
    that when one runs a sequence of operations on a document, an initial cost
    may need to be paid to bring the top-level in sync with the document prior
    to running the first operation in the sequence. *)
val clone : t -> t

(** [copy from to] copies the cursor state from [from] to [to].
    This does **not** rebind the backend.
  *)
val copy : src:t -> dst:t -> unit

(** [materialize d] spaws a new, dedicated Rocq top-level for [d], that starts
    in the same state as the current top-level of [d]. In particular, this new
    top-level is initially only used by [d], and not shared with any clone. If
    the top-level of [d] is not currently shared with any clone, the operation
    is successful but does nothing. An error is returned in case of error when
    spawning the new top-level. *)
val materialize : t -> (unit, string) result

(** [sync d] enforces that the Rocq top-level that is relied on by [d] (and is
    possibly shared with other documents) is in sync with [d]. After a call to
    [sync d], subsequent operations on [d] can be run without paying any extra
    upfront cost. *)
val sync : t -> unit

(** [is_synced d] indicates whether the Rocq toplevel that is relied on by [d]
    is in sync with [d]. If that is the case, subsequent operations on [d] can
    be run witout paying any extra upfront cost. *)
val is_synced : t -> bool

(** [file d] gives the Rocq source file path corresponding to [d]. The file is
    not guaranteed to exist, as the document may have not been committed. Note
    that the returned path exactly corresponds to the argument [file] that was
    initially passed to [init] (it is preserved through [clone]). *)
val file : t -> string

(** [load_file d] reads the Rocq source file corresponding to [d], and appends
    its contents to the document suffix of [d]. If the file does not exist, or
    cannot be fully parsed, an error is returned. *)
val load_file : t -> (unit, string * Rocq_loc.t option) result

(** Data returned by the top-level when running a command. *)
type command_data = Rocq_toplevel.run_data

(** Data returned upon failure of the top-level when running a command. *)
type command_error = Rocq_toplevel.run_error

(** [insert_blanks d ~text] inserts the sequence of blank characters [text] at
    the cursor in document [d], and advances the cursor past them. *)
val insert_blanks : t -> text:string -> unit

(** [insert_command d ~text] inserts, and processes the Rocq command [text] at
    the cursor in document [d]. The cursor is advanced past the command if and
    only if it is processed successfully. In case of failure, an error message
    is returned together with additional information. *)
val insert_command : t -> text:string
  -> (command_data, string * command_error) result

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

val run_step : t ->
  (command_data option, string * command_error option) result

(** [advance_to d ~index] advances the cursor of document [d] to place it just
    before the item with the given [index]. If [index] is invalid, which means
    that it does not point to a valid item index (or one past the index of the
    last item), or that it points to an already processed item, then exception
    [Invalid_argument] is raised. In case of error while processing a command,
    the cursor is left at the reached position, and [Error (loc,msg)] is given
    similarly to what [insert_command] or [run_step] do. *)
val advance_to : t -> index:int -> (unit, string * command_error) result

(** [go_to d ~index] is the same as [advance_to d ~index], but it additionally
    allows to revert to an earlier index like [revert_before d ~index]. In any
    case, no item is erased from the document. If the [index] is invalid, then
    [Invalid_argument] is raised. Valid indices range from [0] to one past the
    index of the last item in the document's suffix. *)
val go_to : t -> index:int -> (unit, string * command_error) result

type processed_item = {
  index : int;
  kind : [`Blanks | `Command | `Ghost];
  off : int;
  text : string;
}

type unprocessed_item = {
  kind : [`Blanks | `Command | `Ghost];
  text : string;
}

val rev_prefix : t -> processed_item list

val suffix : t -> unprocessed_item list

(** [commit ?file ?include_suffix d] commits the contents of document [d] to a
    file. If not target file is specified with [file], the file name specified
    upon document creation is used. Note that if the file exists, it is simply
    overwritten. If [include_suffix] is [true], which is the default, commands
    from the (unprocessed) suffix are also included. The [Sys_error] exception
    is raised upon file system errors. *)
val commit : ?file:string -> ?include_suffix:bool -> t -> unit

val compile : t -> (unit, string) result * string * string

(** [query d ~text] runs the command [text] at the cursor in document [d]. The
    cursor is not moved, and the command is not recorded in the document. Note
    also that the Rocq state is rolled back, to undo any potential side-effect
    that the query would have normally performed. Note that the function gives
    a similar result to [insert_command]. However, feedback is always returned
    immediately in the success case, and no source code location is given when
    an error occurs (queries are not part of the document). *)
val query : t -> text:string -> (command_data, string) result

(** [query_text ?index d ~text] is similar to [query d ~text], but the command
    result is extracted from the feedback, and returned as a string in case of
    success. If [index] is not given, the command [text] is assumed to produce
    exactly one "info" or "notice" feedback item, and its contents is taken as
    result of the query. Otherwise, the [index] identifies the "info"/"notice"
    feedback item to use as result. An [Error] is given when no valid feedback
    item is found. *)
val query_text : ?index:int -> t -> text:string -> (string, string) result

(** [query_text_all ?indices d ~text] is like [query_text d ~text], but it can
    retrieve several "info"/"notice" feedback items at once. When [indices] is
    not given, then the list of all "info"/"notice" items is returned. When an
    [indices] value is given, then a list of same size containing the items at
    corresponding indices is returned. In the case where any of the indices is
    invalid, [Error] is returned. *)
val query_text_all : ?indices:int list -> t -> text:string
  -> (string list, string) result

(** Type of JSON data. *)
type json = Yojson.Safe.t

(** [query_json ?index d ~text] is similar to [query_text ?index d ~text], but
    the result is additionally turned into JSON data. If the command result is
    not a valid JSON string, an [Error] is returned. *)
val query_json : ?index:int -> t -> text:string -> (json, string) result

val query_json_all : ?indices:int list -> t -> text:string
  -> (json list, string) result

val dump : t -> json

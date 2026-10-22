(** Rocq toplevel interface *)

(** {2 Starting and stopping a Rocq toplevel} *)

(** State of a toplevel. *)
type toplevel

(** [init ~args] starts a new Rocq toplevel, with given command-line arguments
    [args]. It is up to the caller to use ["-topfile"] appropriately. If there
    is an error while starting the toplevel, exception [Failure] is raised. *)
val init : args:string list -> toplevel

(** Exception raised when communicating with a stopped top-level. *)
exception Stopped

(** [stop t] stops the top-level [t]. The [Stopped] exception is raised when a
    previous call to [stop] was made on [t]. *)
val stop : toplevel -> unit

(** [fork t] creates a new top-level, initially in the same state as [t]. Note
    that the created top-level is completely independent from [t], and thus it
    can be used concurrently. An error message is given in case of error while
    creating the top-level. *)
val fork : toplevel -> (toplevel, string) result

(** [get_pid t] gives the process identifier of the Rocq top-level attached to
    [t], which should only be useful for debugging. The [Stopped] exception is
    raised if [t] is stopped. *)
val get_pid : toplevel -> int

(** {2 State identifier and backtracking} *)

(** Exception raised if a state identifier is used with the wrong toplevel. *)
exception Toplevel_mismatch

(** State identifier used for backtracking. *)
module StateID : sig
  (** Type of a state identifier, linked to a particular toplevel. *)
  type t

  (** [current t] returns the current state identifier for [t]. *)
  val current : toplevel -> t

  (** [to_int t sid] converts [sid] into an integer (e.g., for serialization).
      It raises [Toplevel_mismatch] if [sid] is not linked to toplevel [t]. *)
  val to_int : toplevel -> t -> int

  (** [unsafe_of_int t i] converts integer [i] into a state identifier that is
      linked to [t]. This operation is unsafe as the user must ensure that [i]
      was obtained via a call to [to_int] using the same toplevel [t]. *)
  val unsafe_of_int : toplevel -> int -> t
end

(** [back_to t ~sid] backtracks the state of toplevel [t] to state [sid]. When
    this operation fails, an error message is provided. This can happen if the
    given [sid] is not reachable anymore. Note that [Stopped] is raised if the
    [stop] function was previously called on [t]. Also, if [sid] is not linked
    to [t], exception [Toplevel_mismatch] is raised. *)
val back_to : toplevel -> sid:StateID.t -> (unit, string) result

(** {2 Running a Rocq command} *)

type quickfix = {
  loc : Loc.t;
  text : string;
}

type feedback_message = {
  level : Feedback.level;
  loc : Loc.t option;
  quickfix : quickfix list;
  text : string;
}

type globrefs_diff = {
  added_constants : Names.Constant.t list;
  removed_constants : Names.Constant.t list;
  added_inductives : Names.MutInd.t list;
  removed_inductives : Names.MutInd.t list;
}

type structured_hyp = {
  name : string;
  def : string option;
  hyp_type : string;
}

type structured_goal = {
  hyps : structured_hyp list;
  goal : string;
}

type proof_state = {
  given_up_goals : int;
  shelved_goals : int;
  unfocused_goals : int list;
  focused_goals : string list;
}

type run_data = {
  globrefs_diff : globrefs_diff;
  feedback_messages : feedback_message list;
  synterp_ast : Rocq_vernac_entry.command;
  proof_state : proof_state option;
  loc : Loc.t option;
}

type run_error = {
  error_loc : Loc.t option;
  feedback_messages : feedback_message list;
  loc : Loc.t option;
}

(** [run t ~loc ~text] runs the vernacular command from [text] in the toplevel
    [t], assuming its first character is at the start of source location [loc]
    (the end of [loc] is ignored). In case of success, a new toplevel state is
    reached, and a value of type [run_data] is returned. In case of failure, a
    value of type [run_error] is returned along with an error message, and the
    state of the toplevel is not updated. The [Stopped] exception is raised if
    [stop] was previously called on [t]. *)
val run : toplevel -> loc:Loc.t -> text:string
  -> (run_data, string * run_error) result

(** [loc_after_blanks t ~loc ~text] returns the source location pointing right
    after the end of [text], assuming that [loc] is a location pointing to the
    start of [text]. The given [text] is expected to consist entirely of blank
    characters and Rocq comments, and an error is returned otherwise. Toplevel
    [t] is used for the operation, but its state is not mutated. *)
val loc_after_blanks : toplevel -> loc:Loc.t -> text:string
  -> (Loc.t, string) result

(** {2 Querying Rocq} *)

(** [structured_goals t] gives the currently focused goals in the toplevel. If
    the [t] is not currently in proof more, then [None] is returned. The state
    of [t] is not changed by calling this function. *)
val structured_goals : toplevel -> structured_goal list option

(** {2 Sentence-splitting} *)

(** AST of a Rocq vernacular command. *)
type command = Rocq_vernac_entry.command

(** Rocq item (vernacular command, or sequence of blank caracters). *)
type item = {
  kind : [`Command of command | `Blanks];
  (** Sentence kind: an actual command or a sequence of blank characters. *)
  text : string;
  (** Full text of the item. *)
  bp : int;
  (** Byte offset of the first character of the item in the file. *)
  ep : int;
  (** Byte offset of the first character after the item in the file. *)
}

(** Data returned by the sentence-splitter. *)
type split_data = {
  items : item list;
  (** List of parsed items. *)
}

(** Data returned in case of sentence-splitting error. *)
type split_error = {
  parsed_items : item list;
  (** Successfully parsed items before the error. *)
  leftover : string;
  (** Text that could not be processed after the parsed items. *)
  error_text : string;
  (** Error message for the error. *)
  error_loc : Loc.t option;
  (** Location for the error, if any. *)
}

(** [split ?sid t ~loc ~text] attempts to parse [text] into a list of items at
    the current toplevel state, or the state [sid] when provided. The location
    [loc] is assumed to start at the first character of [text], and its end is
    ignored. The toplevel state is not mutated by the function. *)
val split : ?sid:StateID.t -> toplevel -> loc:Loc.t -> text:string
  -> (split_data, split_error) result

(** {2 JSON serialization for data returned by [run]} *)

val feedback_message_to_yojson : feedback_message -> Yojson.Safe.t

val globrefs_diff_to_yojson : globrefs_diff -> Yojson.Safe.t

val structured_hyp_to_yojson : structured_hyp -> Yojson.Safe.t

val structured_goal_to_yojson : structured_goal -> Yojson.Safe.t

val proof_state_to_yojson : proof_state -> Yojson.Safe.t

val run_data_to_yojson : run_data -> Yojson.Safe.t

val run_error_to_yojson : run_error -> Yojson.Safe.t

val item_to_yojson : item -> Yojson.Safe.t

val split_data_to_yojson : split_data -> Yojson.Safe.t

val split_error_to_yojson : split_error -> Yojson.Safe.t

(** Rocq toplevel interface *)

(** {2 Starting and stopping a Rocq toplevel} *)

(** State of a toplevel. *)
type toplevel

(** [init ~args] starts a new Rocq toplevel, with given command-line arguments
    [args]. It is up to the caller to use ["-topfile"] appropriately. If there
    is an error while starting the toplevel, exception [Failure] is raised. *)
val init : args:string list -> toplevel

(** Reason why a top-level stopped. *)
type stopped_reason =
  | Normal
  (** The top-level was stopped normally by [stop]. *)
  | Killed
  (** The top-level was forcibly terminated by [kill]. *)
  | Failed of exn
  (** A failure made the top-level unusable; the payload gives its cause. *)

(** Exception raised when communicating with a stopped top-level. Its argument
    gives the reason why the top-level stopped. *)
exception Stopped of stopped_reason

(** Reason why a top-level operation was interrupted. *)
type interrupted_reason =
  | Interrupt
  (** Cooperative interruption completed, and the top-level remains usable. *)
  | Killed
  (** [kill] terminated the top-level while the operation was active. *)
  | Failed of exn
  (** A failure made the top-level unusable; the payload gives its cause. *)

(** Exception raised when a top-level operation is interrupted, indicating how
    the interruption occurred. *)
exception Interrupted of interrupted_reason

(** The [Busy] exception is raised if an operation requires an idle top-level,
    but another operation is active. A top-level may need to be idle to ensure
    exclusive access or to let an operation observe a stable state. *)
exception Busy

(** [stop t] gracefully stops top-level [t]. The [Busy] exception is raised if
    [t] is busy running an operation requiring exclusive top-level access. The
    [Stopped] exception is raised if the top-level was stopped by an operation
    that took effect prior to the current call. *)
val stop : toplevel -> unit

(** [interrupt t] requests cooperative interruption of the operation currently
    running on [t], if any. The [back_to] operation ignores [interrupt] calls.
    Exception [Stopped] is raised if the top-level was stopped by an operation
    that took effect prior to the interruption. *)
val interrupt : toplevel -> unit

(** [kill t] forcibly stops top-level [t]. Any operation still active when the
    termination takes effect is interrupted. The [Stopped] exception is raised
    if the top-level was stopped by an operation that took effect prior to the
    current call. *)
val kill : toplevel -> unit

(** [fork t] creates a new top-level, initially in the same state as [t]. Note
    that the created top-level has independent channels and can be used safely
    concurrently. It retains the identity of [t], so all state identifiers for
    their shared history remain valid on either top-level. Creation errors are
    returned as error messages. The [Busy] exception is raised whenever [t] is
    busy with an operation that requires exclusive top-level access. Exception
    [Interrupted] is raised upon interruption. Finally, [Stopped] is raised if
    [t] was already stopped. *)
val fork : toplevel -> (toplevel, string) result

(** [get_pid t] gives the process identifier of the Rocq top-level attached to
    [t], which should only be useful for debugging. The [Stopped] exception is
    raised if [t] was already stopped. *)
val get_pid : toplevel -> int

(** {2 State identifier and backtracking} *)

(** Exception raised for a state identifier from another top-level lineage. *)
exception Toplevel_mismatch

(** State identifier used for backtracking. *)
module StateID : sig
  (** Type of a state identifier, linked to a particular top-level lineage. *)
  type t

  (** [current t] gives the current state identifier for top-level [t]. [Busy]
      is raised if an operation requiring exclusive top-level access is active
      on [t]. The [Stopped] exception is raised if [t] was already stopped. *)
  val current : toplevel -> t

  (** [to_int t sid] converts [sid] into an integer (e.g., for serialization).
      It raises [Toplevel_mismatch] if [sid] has another top-level lineage. *)
  val to_int : toplevel -> t -> int

  (** [unsafe_of_int t i] converts integer [i] into a state identifier that is
      linked to the lineage of [t]. This is unsafe, and the caller must ensure
      that [i] was obtained by calling [to_int] with a top-level from the same
      lineage. *)
  val unsafe_of_int : toplevel -> int -> t
end

(** [back_to t ~sid] backtracks the state of toplevel [t] to state [sid]. When
    this operation fails, an error message is provided. This can happen if the
    given [sid] is not reachable anymore. The [Toplevel_mismatch] exception is
    raised if [sid] is not linked to top-level [t]. Exception [Busy] is raised
    if [t] is busy with an operation that requires exclusive top-level access.
    Calls to [interrupt t] have no effect while the operation is active, since
    Rocq cannot reliably restore its state before the requested backtrack. The
    [Interrupted] exception can also be raised when the top-level is killed or
    fails. Finally, [Stopped] is raised if [t] was already stopped. *)
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
    state of the toplevel is not updated. Exceptions [Stopped], [Interrupted],
    and [Busy] are raised under the same conditions as for [fork]. *)
val run : toplevel -> loc:Loc.t -> text:string
  -> (run_data, string * run_error) result

(** [loc_after_blanks t ~loc ~text] returns the source location pointing right
    after the end of [text], assuming that [loc] is a location pointing to the
    start of [text]. The given [text] is expected to consist entirely of blank
    characters and Rocq comments, and an error is returned otherwise. Toplevel
    [t] is used for the operation, but its state is not mutated. The exception
    behaviour is the same as for [run] or [fork]. *)
val loc_after_blanks : toplevel -> loc:Loc.t -> text:string
  -> (Loc.t, string) result

(** {2 Querying Rocq} *)

(** [structured_goals t] gives the currently focused goals in the toplevel. If
    the [t] is not currently in proof mode, then [None] is returned. The state
    of [t] is not changed by calling this function. Exceptions are raised like
    for [run] or [fork]. *)
val structured_goals : toplevel -> structured_goal list option

(** {2 Sentence-splitting} *)

(** AST of a Rocq vernacular command. *)
type command = Rocq_vernac_entry.command

(** Rocq item (vernacular command, or sequence of blank characters). *)
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
    ignored. The toplevel state is not mutated by the function. Exceptions are
    raised as for [run] and [fork]. [Toplevel_mismatch] is raised if [sid] and
    [t] have different top-level lineages. *)
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

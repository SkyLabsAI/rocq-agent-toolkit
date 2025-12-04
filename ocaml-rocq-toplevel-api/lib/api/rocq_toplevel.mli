(** Rocq toplevel interface *)

(** {2 Starting and stopping a Rocq toplevel} *)

(** State of a toplevel. *)
type toplevel

(** [init ~args] starts a new Rocq toplevel, with given command-line arguments
    [args]. It is up to the caller to use ["-topfile"] appropriately. *)
val init : args:string list -> toplevel

(** Exception raised when communicating with a stopped top-level. *)
exception Stopped

(** [stop t] stops the top-level [t]. The [Stopped] exception is raised when a
    previous call to [stop] was made on [t]. *)
val stop : toplevel -> unit

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
  loc : Rocq_loc.t;
  text : string;
}

type feedback_message = {
  level : Feedback.level;
  loc : Rocq_loc.t option;
  quickfix : quickfix list;
  text : string;
}

type globrefs_diff = {
  added_constants : Names.Constant.t list;
  removed_constants : Names.Constant.t list;
  added_inductives : Names.MutInd.t list;
  removed_inductives : Names.MutInd.t list;
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
  proof_state : proof_state option;
}

type run_error = {
  error_loc : Rocq_loc.t option;
  feedback_messages : feedback_message list;
}

(** [run t ~off ~text] runs the vernacular command from [text] in the toplevel
    [t], assuming its first character is at byte offset [off] in the processed
    "file". Upon success, a new toplevel state is reached, and a value of type
    [run_data] is returned. In case of failure, an error message together with
    a value of type [run_error] is returned, and the state is not updated. The
    [Stopped] exception is raised if [stop] was previously called on [t]. *)
val run : toplevel -> off:int -> text:string
  -> (run_data, string * run_error) result

(** {2 JSON serialization for data returned by [run]} *)

val feedback_message_to_yojson : feedback_message -> Yojson.Safe.t

val globrefs_diff_to_yojson : globrefs_diff -> Yojson.Safe.t

val proof_state_to_yojson : proof_state -> Yojson.Safe.t

val run_data_to_yojson : run_data -> Yojson.Safe.t

val run_error_to_yojson : run_error -> Yojson.Safe.t

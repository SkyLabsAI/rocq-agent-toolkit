(** Rocq toplevel interface.

    In the current version, if a communication error occurs with the toplevel,
    the library aborts the whole program with [exit 1]. *)

(** {2 Starting and stopping a Rocq toplevel} *)

(** State of a toplevel. *)
type t

(** [init ~args ~file] starts a toplevel for [file] with the Rocq command-line
    arguments [args]. *)
val init : args:string list -> file:string -> t

(** Exception raised by all subsequent functions taking a value of type [t] as
    input, in the case where the corresponding toplevel is stopped. *)
exception Stopped

(** [stop t] stops the toplevel [t]. *)
val stop : t -> unit

(** {2 State identifier} *)

(** State identifier used for backtracking. *)
module StateId : sig
  (** Type of a state identifier. *)
  type t

  (** [to_json sid] converts [sid] into JSON data. *)
  val to_json : t -> Yojson.Safe.t

  (** [of_json json] attempts to convert the JSON data [json] into a state
      identifier, and panics if it fails. The operation is guaranteed to
      succeed if [json] was produced by a call to [to_json]. *)
  val of_json : Yojson.Safe.t -> t
end

(** [get_state_id t] gives the current state identifier for toplevel [t]. The
    [Stopped] exception is raised if [t] is already stopped. *)
val get_state_id : t -> StateId.t

(** {2 Queries} *)

(** Rocq source code location, if any. *)
type loc = Rocq_loc.t option

(** Exception raised by [back_to] and [show_goal] in the case where the given
    [StateId.t] was obtained from a different toplevel. *)
exception Toplevel_mismatch

(** [back_to t ~sid] backtracks the state of toplevel [t] to state [sid], or
    gives an error message. Exception [Toplevel_mismatch] is raised without
    a query being emitted if [sid] was not issued for [t]. *)
val back_to : t -> sid:StateId.t -> (unit, string) result

(** [show_goal t ~sid ~gid] returns the goal identifier by [gid] in the state
    [sid] for toplevel [t], or gives an error message. As for [back_to], the
    [Toplevel_mismatch] exception is raised if [sid] is not valid for [t]. *)
val show_goal : t -> sid:StateId.t -> gid:int -> (string, string) result

(** [run t ~off ~text] runs the vernacular command from [text] in the toplevel
    [t], assuming its first character is at byte offset [off] in the "file".
    If there are open goals after the command, they are returned. In case of
    error, a location and error message is provided. *)
val run : t -> off:int -> text:string -> (string option, loc * string) result

(** {2 Feedback} *)

(** Rocq feedback message. *)
type feedback = {
  kind : [`Debug | `Info | `Notice | `Warning | `Error];
  text : string;
  loc  : loc;
}

(** Exception raised by [get_feedback]. *)
exception No_feedback

(** [get_feedback t] gives returns all feedback messages attached to the last
    query that was run in toplevel [t]. Exception [No_feedback] is raised if
    no request was run in [t] yet. *)
val get_feedback : t -> feedback list

(** Simple Request / Response Loop

    This module allows constructing simple request-response loops based on the
    JSON-RPC Transport Protocol. A request loop handles requests sequentially,
    sending corresponding responses in order. A request loop initially handles
    only one request method called ["quit"], without parameters, that ends the
    request loop. *)

(** Parameter specification. *)
module Params : sig
  (** Type of a tag type. *)
  type 'a tag

  (** [int] is a tag specifying an integer argument. *)
  val int : int tag

  (** [bool] is a tag specifying a boolean argument. *)
  val bool : bool tag

  (** [string] is a tag specifying a string argument. *)
  val string : string tag

  (** [option t] specifies an optional argument whose type has tag [t]. *)
  val option : 'a tag -> 'a option tag

  (** [list t] is a tag specifying a list argument. Argument [t] specifies the
      uniform type of the contained arguments. *)
  val list : 'a tag -> 'a list tag

  (** Specification of a list of parameters. *)
  type 'a t

  (** [nil] specifies an empty parameter list. *)
  val nil : unit t

  (** [cons tag spec] extends parameter specification [spec], by prepending it
      with [tag]. For example [cons int (cons bool nil)] specifies a parameter
      list that contains (in order) an integer and a boolean, which leads to a
      the type [int * (bool * unit)] for parameters. *)
  val cons : 'a tag -> 'b t -> ('a * 'b) t
end

(** Dynamically constructed set of requests, with state of type ['a]. *)
type 'a t

(** [create ()] initialises a new set of requests. The only handled request at
    creation time is a special ["quit"] request, which can be used to exit the
    request-response loop. The type parameter indicates what type of state the
    requests manipulate. *)
val create : unit -> 'a t

(** Type of the implementation of a request. A request implementation can rely
    on the [Invalid_arguments] exception to signal failed parameter validation
    (e.g., index out of bounds). Other exceptions are not caught. *)
type ('a, 'b) action =
  'a -> 'b -> 'a * (Yojson.Safe.t, Yojson.Safe.t option * string) result

(** [add rset name pspec a] extends [req] with an handler for a request called
    [name], with parameters specified by [pspec], and implemented by [a]. If a
    handler was already defined for a request named [name], then the exception
    [Invalid_argument] is raised. *)
val add : 'a t -> string -> 'b Params.t -> ('a, 'b) action -> unit

(** Exception raised by [run] in case of protocol error. *)
exception Error of string

(** [run rset ~ic ~oc s] starts a request / response loop. It expects requests
    on the input channel [ic], and sends corresponding responses on the output
    channel [oc]. The set of supported requests is specified by [rset], and it
    can be extended dynamcally. State (of type ['a]) is threaded through every
    request handler. The initial state is given by [s], and the function gives
    back the final state at the end. Exception [Error] is raised upon protocol
    errors. *)
val run : 'a t -> ic:In_channel.t -> oc:Out_channel.t -> 'a -> 'a

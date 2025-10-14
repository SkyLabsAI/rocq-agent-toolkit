(** Handle to an object type of the API. The type parameter indicates how this
    object type is represented in OCaml. *)
type 'a api_obj

(** JSON data. *)
type json = Yojson.Safe.t

(** Data schema. *)
module Schema : sig
  (** Representation of a data schema, with its OCaml representation. *)
  type _ t

  (** [null] is a schema specifying a "null" value. *)
  val null : unit t

  (** [any] is a schema specifying an arbitrary JSON value. *)
  val any : json t

  (** [int] is a schema specifying an integer value. *)
  val int : int t

  (** [bool] is a schema specifying a boolean value. *)
  val bool : bool t

  (** [string] is a schema specifying a string value. *)
  val string : string t

  (** [nullable s] is a schema that specifies either the same kind of value as
      [s], or a "null" value. The interpretation is [None] in the latter case,
      and [Some(_)] otherwise. *)
  val nullable : 'a t -> 'a option t

  (** [list s] is a schema that specifies a list of values whose kind is given
      by schema [s]. *)
  val list : 'a t -> 'a list t

  (** [obj k] is a schema that specifies an object as specified by [k]. *)
  val obj : 'a api_obj -> 'a t
end

(** Object fields. *)
module Fields : sig
  (** Description of an object's fields. *)
  type 'a t

  (** [nil] denotes the empty list of object fields. *)
  val nil : unit t

  (** [add ~name ?descr s fs] extends the object fields [fs] with a new field.
      The new fields is named [name], and its type is specified by [s]. If aim
      of the [descr] field is to document what the field represents. Exception
      [Invalid_argument] is raised if [fs] already contains a field [name]. *)
  val add : name:string -> ?descr:string -> 'a Schema.t -> 'b t -> ('a * 'b) t
end

(* Type of an API whose internal state is specified by the type parameter. *)
type _ api

(** [create ()] builds a new, empty API. *)
val create : unit -> 'a api

(** [declare_object api ~name ?descr ~encode ~decode fs] declares a new object
    type in the given [api]. This declared object is given type [name], and it
    holds the fields specified by [fs]. Similarly to [Fields.add], [descr] can
    be used to document what the object type represent. The [encode] function,
    and its inverse [decode], can be used to specify a higher-level OCaml type
    for an object's representation. The exception [Invalid_argument] is raised
    if an object [name] was already declared in [api]. *)
val declare_object : _ api -> name:string -> ?descr:string
  -> encode:('a -> 'b) -> decode:('b -> 'a) -> 'a Fields.t -> 'b api_obj

(** [declare api ~name ... impl] declares a new method [name], implemented via
    the [impl] function, in the given [api]. Argument [descr], when specified,
    documents the action of the method at a high level. The [arg] argument may
    be used to specify the arguments expected by the method, and documentation
    for the argument type may be provided with [arg_descr]. The [ret] argument
    can be used, together with [ret_descr], to specify the return type. If the
    [name] was previously used in a method declaration in [api], the exception
    [Invalid_argument] is raised. Moreover, the [impl] function is not allowed
    to raise exceptions (this is undefined behaviour). *)
val declare : 's api -> name:string -> ?descr:string
  -> arg:'a Schema.t -> ?arg_descr:string
  -> ret:'b Schema.t -> ?ret_descr:string
  -> ('s -> 'a -> 's * 'b) -> unit

(** [declare_full api ~name ...] is similar to [declare api ~name ...], but it
    allows a more general form of implementation that can report an error. The
    [recoverable] argument ([true] by default) indicates whether errors can be
    recovered from (i.e., if subsequent queries are possible). Arguments [err]
    and [err_descr] are used to specify the payload in case of error. *)
val declare_full : 's api -> name:string -> ?descr:string
  -> arg:'a Schema.t -> ?arg_descr:string
  -> ret:'b Schema.t -> ?ret_descr:string
  -> err:'e Schema.t -> ?err_descr:string
  -> ?recoverable:bool
  -> ('s -> 'a -> 's * ('b, 'e * string) Result.t) -> unit

(** [run api ~ic ~oc s] starts an interactive request/response loop for [api].
    Requests are expected on channel [ic], and the corresponding responses are
    sent to channel [oc]. The set of supported requests is specified by [api],
    and it can be extended dynamically. The API state, with initial value [s],
    is threaded through all request handlers. If the end of file is reached on
    [ic], or if the special ["quit"] request is received, the function returns
    the API state. An [Error] is returned only in case of protocol error. *)
val run : 's api -> ic:In_channel.t -> oc:Out_channel.t
  -> 's -> ('s, string) Result.t

(** [output_docs oc api] outputs markdown-formatted documentation for [api] to
    the output channel [oc]. *)
val output_docs : Out_channel.t -> _ api -> unit

(** [output_python_api oc api] outputs python bindings for [api] to the output
    channel [oc]. *)
val output_python_api : Out_channel.t -> _ api -> unit

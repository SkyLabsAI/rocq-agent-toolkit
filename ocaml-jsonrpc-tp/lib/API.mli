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

  (** [variant] is a schema specifying an alternative of literal values. *)
  val variant : values:'a list -> default:'a -> encode:('a -> string) -> 'a t

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

(** Method arguments. *)
module Args : sig
  (** Description of a method's arguments. *)
  type 'a t

  (** [nil] denotes the empty list of arguments. *)
  val nil : unit t

  (** [add ~name ?descr s args] adds a new argument named [name] to [args]. It
      has a type specified by [s], and is optionally described by [descr]. The
      [Invalid_argument] exception is raised in the case where [name] was used
      in [args] already. *)
  val add : name:string -> ?descr:string -> 'a Schema.t -> 'b t -> ('a * 'b) t
end

(* Type of an API whose internal state is specified by the type parameter. *)
type _ api

(** [create ~name] builds a new, empty API. The given [name] is used as Python
    class name when a Python API is generated. *)
val create : name:string -> 'a api

(** [declare_object api ~name ?descr ?default ~encode ~decode fs]  declares  a
    new object type [name],  with fields [fs] and an optional [default] value,
    in the given [api]. Like for [Fields.add], [descr] can be used to document
    what the object type represent. The [encode] and [decode] functions may be
    used to specify a higher-level OCaml type for the object's representation.
    Exception [Invalid_argument] is raised if an object of the same [name] was
    already declared in [api]. *)
val declare_object : _ api -> name:string -> ?descr:string -> ?default:'b
  -> encode:('a -> 'b) -> decode:('b -> 'a) -> 'a Fields.t -> 'b api_obj

(** [declare api ~name ... impl] declares a new method [name], implemented via
    the [impl] function, in the given [api]. Argument [descr], when specified,
    documents the action of the method at a high level. The [args] argument is
    used to specify the arguments expected by the method, and [ret] is used to
    specify the return type.  The [ret_descr] can be used to describe what the
    return value represents. If [name] collides with the name of a method that
    was previously declared in [api],  exception [Invalid_argument] is raised.
    Note that if [impl] raises [Invalid_argument], then the method will return
    with an error indicating that the passed parameters are invalid (e.g., one
    argument is not in bounds). Raising any other exception leads to undefined
    behaviour. *)
val declare : 's api -> name:string -> ?descr:string -> args:'a Args.t
  -> ret:'b Schema.t -> ?ret_descr:string
  -> ('s -> 'a -> 's * 'b) -> unit

(** [declare_full api ~name ...] is similar to [declare api ~name ...], but it
    allows a more general form of implementation that can report an error. The
    [recoverable] argument ([true] by default) indicates whether errors can be
    recovered from (i.e., if subsequent queries are possible). Arguments [err]
    and [err_descr] are used to specify the payload in case of error. *)
val declare_full : 's api -> name:string -> ?descr:string -> args:'a Args.t
  -> ret:'b Schema.t -> ?ret_descr:string
  -> err:'e Schema.t -> ?err_descr:string
  -> ?recoverable:bool
  -> ('s -> 'a -> 's * ('b, string * 'e) Result.t) -> unit

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

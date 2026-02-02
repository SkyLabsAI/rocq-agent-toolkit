(** Generic, parallel, JSON-RPC 2.0 server. *)

(** Type of JSON values. *)
type json = Yojson.Safe.t

(** Type of request / notification parameters. *)
type params = [ `Assoc of (string * json) list | `List of json list ] option

(** Request response. *)
module Response : sig
  (** Type of a request response. *)
  type t

  (** Type of an error response code. *)
  type error_code =
    | ParseError
    | InvalidRequest
    | MethodNotFound
    | InvalidParams
    | InternalError
    | ServerErrorStart
    | ServerErrorEnd
    | ServerNotInitialized
    | UnknownErrorCode
    | RequestFailed
    | ServerCancelled
    | ContentModified
    | RequestCancelled
    | Other of int

  (** [ok data] builds a response withe the given payload [data]. *)
  val ok : json -> t

  (** [error ?code ?data s] builds an error response with the given [code] (by
      default [RequestFailed]), optional payload [data], and message [s]. *)
  val error : ?code:error_code -> ?data:json -> string -> t
end

(** Type of a request handler function. A handler receives the method name (as
    argument [name]), its parameters (as argument [params], and a notification
    function (as argument [notify]). The notification function can be used any
    number of times, e.g., to notify the client of progress, before building a
    response. Undefined behaviour is produced if the [notify] function is used
    after the handler has returned. *)
type request_handler =
  name:string ->
  params:params ->
  notify:(name:string -> params:params -> unit) ->
  Response.t

(** Type of a notification handler function. The only difference with handlers
    for requests is that no response is produced. *)
type notification_handler =
  name:string ->
  params:params ->
  notify:(name:string -> params:params -> unit) ->
  unit

(** [run ~ic ~oc ~workers ~handle_request ~handle_notification] runs a service
    serving JSON-RPC 2.0 requests on channel [ic], and responding on [oc]. The
    [workers] parameter specifies how many worker threads should be spawned to
    handle requests and notifications using the functions [handle_request] and
    [handle_notification]. The function returns an error message upon any kind
    of protocol error. The service only stops if [ic] reaches the end of file,
    but not after all queued requests / notifications are handled. An error is
    only returned in case of protocol error. *)
val run :
  ic:In_channel.t ->
  oc:Out_channel.t ->
  workers:int ->
  handle_request:request_handler ->
  handle_notification:notification_handler ->
  (unit, string) Result.t

(** [run_seq ~ic ~oc ~handle_request ~handle_notification] is similar to [run]
    applied to the same parameters, but interactions on the channels are fully
    sequential (and blocking). In particular, the client should issue requests
    one at a time,  and wait for the corresponding response before issuing any
    subsequent request. No such restriction is imposed on notifications, since
    the client does not need to wait for a response. If notifications are sent
    by the request handler durring its run, they are received by the client as
    it is expecting a response. The client is required to accept any number of
    notification packets until it receives the response to the request. As the
    client is never ready to receive a notification after having itself issued
    a notification, the notification handler always drops notification. *)
val run_seq :
  ic:In_channel.t ->
  oc:Out_channel.t ->
  handle_request:request_handler ->
  handle_notification:notification_handler ->
  (unit, string) Result.t

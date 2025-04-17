module Params = struct
  type 'a tag =
    | Int    : int    tag
    | Bool   : bool   tag
    | String : string tag

  let int    : int    tag = Int 
  let bool   : bool   tag = Bool
  let string : string tag = String

  type 'a t =
    | Nil : unit t
    | Cns : 'a tag * 'b t -> ('a * 'b) t

  let nil : unit t = Nil

  let cons : 'a tag -> 'b t -> ('a * 'b) t = fun tag spec ->
    Cns(tag, spec)
end

type ('a, 'b) action =
  'a -> 'b -> 'a * (Yojson.Safe.t, Yojson.Safe.t option * string) result

type 'a command = C : 'b Params.t * ('a, 'b) action -> 'a command

type 'a t = {handlers : (string, 'a command) Hashtbl.t}

let create : unit -> 'a t = fun _ ->
  {handlers = Hashtbl.create 13}

let add : 'a t -> string -> 'b Params.t -> ('a, 'b) action -> unit =
    fun rset f ty a ->
  if f = "quit" || Hashtbl.mem rset.handlers f then
    invalid_arg "Jsonrpc_tp_loop.add";
  Hashtbl.add rset.handlers f (C(ty, a))

exception Error of string

let error : string -> 'a = fun s ->
  raise (Error("Error: " ^ s ^ "."))

module J = Jsonrpc

module Response = struct
  let error ~oc id ?data code message =
    let e = J.Response.Error.make ?data ~code ~message () in
    let r = J.Response.error id e in
    Jsonrpc_tp.send ~oc (J.Packet.Response(r))

  let method_not_found ~oc id f =
    let message = Printf.sprintf "Method %s not found." f in
    error ~oc id J.Response.Error.Code.MethodNotFound message

  let invalid_params ~oc id f =
    let message = Printf.sprintf "Invalid parameters for method %s." f in
    error ~oc id J.Response.Error.Code.InvalidParams message

  let reply ~oc id payload =
    let response = J.Response.ok id payload in
    Jsonrpc_tp.send ~oc (J.Packet.Response(response))

  let ok ~oc id =
    reply ~oc id `Null
end

type json = Yojson.Safe.t

let rec parse_params : type a. a Params.t -> json list -> a option =
    fun spec params ->
  let open Params in
  match (spec, params) with
  | (Nil             , []                  ) -> Some(())
  | (Cns(Int   ,spec), `Int(i)    :: params) ->
      let args = parse_params spec params in
      Option.map (fun args -> (i, args)) args
  | (Cns(Bool  ,spec), `Bool(b)   :: params) ->
      let args = parse_params spec params in
      Option.map (fun args -> (b, args)) args
  | (Cns(String,spec), `String(s) :: params) ->
      let args = parse_params spec params in
      Option.map (fun args -> (s, args)) args
  | (_               , _                   ) -> None

let run : 'a t -> ic:In_channel.t -> oc:Out_channel.t -> 'a -> 'a =
    fun rset ~ic ~oc st ->
  let rec loop st =
    match Jsonrpc_tp.recv ~ic () with
    | Error(msg)  -> error msg
    | Ok(None)    -> st
    | Ok(Some(p)) ->
    let J.Request.{id; method_ = f; params} =
      match p with
      | J.Packet.Request(r) -> r
      | _                   -> error "not a request packet"
    in
    match (f, params) with
    | ("quit", None           ) -> Response.ok ~oc id; st
    | ("quit", Some(`List([]))) -> Response.ok ~oc id; st
    | ("quit", _              ) -> Response.invalid_params ~oc id f; loop st
    | (_     , _              ) ->
    match Hashtbl.find_opt rset.handlers f with
    | None            -> Response.method_not_found ~oc id f; loop st
    | Some(C(spec,a)) ->
    let params =
      match params with
      | None                -> Some([])
      | Some(`List([]    )) -> Some([])
      | Some(`List(params)) -> Some(params)
      | _                   -> None (* Unexpected shape, invalid. *)
    in
    match params with
    | None         -> Response.invalid_params ~oc id f; loop st
    | Some(params) ->
    match parse_params spec params with
    | None         -> Response.invalid_params ~oc id f; loop st
    | Some(params) ->
    let (st, res) = a st params in
    let response =
      match res with
      | Ok(data)             -> J.Response.ok id data
      | Error(data, message) ->
          let code = J.Response.Error.Code.RequestFailed in
          J.Response.error id (J.Response.Error.make ?data ~code ~message ())
    in
    Jsonrpc_tp.send ~oc (J.Packet.Response(response));
    loop st
  in
  loop st

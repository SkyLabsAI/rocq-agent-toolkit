module Params = struct
  type 'a tag =
    | Int    : int    tag
    | Bool   : bool   tag
    | String : string tag
    | Option : 'a tag -> 'a option tag
    | List   : 'a tag -> 'a list tag

  let int    : int    tag = Int 
  let bool   : bool   tag = Bool
  let string : string tag = String

  let option : 'a tag -> 'a option tag = fun t -> Option(t)
  let list : 'a tag -> 'a list tag = fun t -> List(t)

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

  let invalid_params ~oc id ?msg f =
    let message =
      let msg = match msg with None -> "" | Some(msg) -> ": " ^ msg in
      Printf.sprintf "Invalid parameters for method %s%s." f msg
    in
    error ~oc id J.Response.Error.Code.InvalidParams message

  let reply ~oc id payload =
    let response = J.Response.ok id payload in
    Jsonrpc_tp.send ~oc (J.Packet.Response(response))

  let ok ~oc id =
    reply ~oc id `Null
end

type json = Yojson.Safe.t

type 'a tag = 'a Params.tag

let rec parse_param : type a. a tag -> json -> a option = fun t p ->
  match (t, p) with
  | (Int      , `Int(i)   ) -> Some(i)
  | (Bool     , `Bool(b)  ) -> Some(b)
  | (String   , `String(s)) -> Some(s)
  | (Option(t), _         ) -> parse_option t p
  | (List(t)  , `List(l)  ) -> parse_list t l
  | (_        , _         ) -> None

and parse_option : type a. a tag -> json -> a option option = fun t p ->
  match p with
  | `Null -> Some(None)
  | _     -> Option.map (fun o -> Some(o)) (parse_param t p)

and parse_list : type a. a tag -> json list -> a list option = fun t l ->
  let rec parse_list rev_acc xs =
    match xs with
    | []      -> Some(List.rev rev_acc)
    | x :: xs ->
    match parse_param t x with
    | None    -> None
    | Some(p) -> parse_list (p :: rev_acc) xs
  in
  parse_list [] l

let rec parse_params : type a. a Params.t -> json list -> a option =
    fun spec params ->
  let open Params in
  match (spec, params) with
  | (Nil         , []             ) -> Some(())
  | (Nil         , _     :: _     ) -> None
  | (Cns(_, _   ), []             ) -> None
  | (Cns(t, spec), param :: params) ->
  match parse_param t param with
  | None         -> None
  | Some(param)  ->
  match parse_params spec params with
  | None         -> None
  | Some(params) -> Some((param, params))

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
    let st =
      try
        let (st, res) = a st params in
        let response =
          match res with
          | Ok(data)             -> J.Response.ok id data
          | Error(data, message) ->
              let code = J.Response.Error.Code.RequestFailed in
              let err = J.Response.Error.make ?data ~code ~message () in
              J.Response.error id err
        in
        Jsonrpc_tp.send ~oc (J.Packet.Response(response)); st
      with Invalid_argument(msg) ->
        Response.invalid_params ~oc id f ~msg; st
    in
    loop st
  in
  loop st

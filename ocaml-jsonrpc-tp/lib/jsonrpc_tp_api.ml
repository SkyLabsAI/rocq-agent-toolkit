type 'a api_obj = string

type json = Yojson.Safe.t

module Schema = struct
  type _ t =
    | Null : unit t
    | Any : json t
    | Int : int t
    | Bool : bool t
    | String : string t
    | Nullable : 'a t -> 'a option t
    | List : 'a t -> 'a list t
    | Obj : 'a api_obj -> 'a t

  let null = Null
  let any = Any
  let int = Int
  let bool = Bool
  let string = String
  let nullable s = Nullable(s)
  let list s = List(s)
  let obj o = Obj(o)

  let rec descr : type a. a t -> string = fun s ->
    match s with
    | Null -> "a `null` value"
    | Any -> "a JSON value"
    | Int -> "an integer"
    | Bool -> "a boolean"
    | String -> "a string"
    | Nullable s -> "either `null` or " ^ descr s
    | List s -> "a list where each element is " ^ descr s
    | Obj o -> "an instance of the `" ^ o ^ "` object"

  let is_default : type a. a t -> a -> bool = fun s v ->
    match (s, v) with
    | (Bool       , false) -> true
    | (List(_)    , []   ) -> true
    | (Nullable(_), None ) -> true
    | (_          , _    ) -> false

  let default : type a. a t -> a option = fun s ->
    match s with
    | Bool        -> Some(false)
    | List(_)     -> Some([])
    | Nullable(_) -> Some(None)
    | _           -> None
end

module Fields = struct
  type _ t =
    | Nil : unit t
    | Cns : {
        name : string;
        descr : string option;
        schema : 'a Schema.t;
        fields : 'b t
      } -> ('a * 'b) t

  let nil = Nil
  let add ~name ?descr schema fields =
    Cns({name; descr; schema; fields})
end

type _ obj =
  | O : {
      name : 'b api_obj;
      descr : string option;
      fields : 'a Fields.t;
      encode : ('a -> 'b);
      decode : ('b -> 'a);
    } -> 'b obj

type any_obj = A : 'a obj -> any_obj
[@@unboxed]

module SMap = Map.Make(String)

type 's api_method =
  | Pure : {
      name : string;
      descr : string option;
      arg : 'a Schema.t;
      arg_descr : string option;
      ret : 'b Schema.t;
      ret_descr : string option;
      impl : ('s -> 'a -> 's * 'b);
    } -> 's api_method
  | Rslt : {
      name : string;
      descr : string option;
      arg : 'a Schema.t;
      arg_descr : string option;
      ret : 'b Schema.t;
      ret_descr : string option;
      err : 'e Schema.t;
      err_descr : string option;
      recoverable : bool;
      impl : ('s -> 'a -> 's * ('b, 'e * string) Result.t);
    } -> 's api_method

type 's api = {
  mutable api_objects : any_obj list;
  mutable api_methods : 's api_method SMap.t;
}

let get_obj : type a. _ api -> a api_obj -> a obj = fun api k ->
  match List.find_opt (fun (A(O(o))) -> o.name = k) api.api_objects with
  | None       -> assert false
  | Some(A(o)) -> Obj.magic o

let create : unit -> _ api = fun _ ->
  {api_objects = []; api_methods = SMap.empty}

let duplicate fname =
  raise (Invalid_argument("Jsonrpc_tp_api." ^ fname ^ ": duplicate name"))

let declare_object api ~name ?descr ~encode ~decode fields =
  match List.exists (fun (A(O(r))) -> r.name = name) api.api_objects with
  | true  -> duplicate "declare_object"
  | false ->
  let o = A(O({name; descr; fields; encode; decode})) in
  api.api_objects <- o :: api.api_objects; name

let declare api ~name ?descr ~arg ?arg_descr ~ret ?ret_descr impl =
  match SMap.mem name api.api_methods with
  | true  -> duplicate "declare"
  | false ->
  let m = Pure({name; descr; arg; arg_descr; ret; ret_descr; impl}) in
  api.api_methods <- SMap.add name m (api.api_methods)

let declare_full api ~name ?descr ~arg ?arg_descr ~ret ?ret_descr
    ~err ?err_descr ?(recoverable=true) impl =
  match SMap.mem name api.api_methods with
  | true  -> duplicate "declare_full"
  | false ->
  let m =
    Rslt({
      name; descr; arg; arg_descr; ret; ret_descr; err; err_descr;
      recoverable; impl;
    })
  in
  api.api_methods <- SMap.add name m (api.api_methods)

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

let rec to_json : type a. _ api -> a Schema.t -> a -> json = fun api s v ->
  match (s, v) with
  | (Null       , ()     ) -> `Null
  | (Any        , _      ) -> v
  | (Int        , _      ) -> `Int(v)
  | (Bool       , _      ) -> `Bool(v)
  | (String     , _      ) -> `String(v)
  | (Nullable(_), None   ) -> `Null
  | (Nullable(s), Some(v)) -> to_json api s v
  | (List(s)    , _      ) -> `List(List.map (to_json api s) v)
  | (Obj(o)     , _      ) ->
  let O(o) = get_obj api o in
  let rec make : type a. a Fields.t -> a -> (string * json) list = fun fs v ->
    let open Fields in
    match (fs, v) with
    | (Nil                              , ()     ) -> []
    | (Cns({name; schema; fields=fs; _}), (v, vs)) ->
    match Schema.is_default schema v with
    | true  -> make fs vs
    | false -> (name, to_json api schema v) :: make fs vs
  in
  `Assoc(make o.fields (o.decode v))

let of_json : type a. _ api -> a Schema.t -> json -> (a, string) Result.t =
    fun api s json ->
  let exception Error of string in
  let error s = raise (Error(s)) in
  let rec of_json : type a. a Schema.t -> json -> a = fun s json ->
    let of_json_obj : type a. a api_obj -> _ = fun o fields ->
      let O(o) = get_obj api o in
      let rec make : type a. a Fields.t -> a = fun fs ->
        let open Fields in
        match fs with
        | Nil                               -> ()
        | Cns({name; schema; fields=fs; _}) ->
        match List.assoc_opt name fields with
        | Some(json) -> (of_json schema json, make fs)
        | None       ->
        match Schema.default schema with
        | Some(v)    -> (v, make fs)
        | None       -> error ("missing object field \"" ^ name ^ "\"")
      in
      o.encode (make o.fields)
    in
    match (s, json) with
    | (Null       , `Null     ) -> ()
    | (Null       , _         ) -> error "expected null value"
    | (Any        , _         ) -> json
    | (Int        , `Int(i)   ) -> i
    | (Int        , _         ) -> error "expected integer value"
    | (Bool       , `Bool(b)  ) -> b
    | (Bool       , _         ) -> error "expected boolean value"
    | (String     , `String(s)) -> s
    | (String     , _         ) -> error "expected string value"
    | (Nullable(_), `Null     ) -> None
    | (Nullable(s), _         ) -> Some(of_json s json)
    | (List(s)    , `List(vs) ) -> List.map (of_json s) vs
    | (List(_)    , _         ) -> error "expected list value"
    | (Obj(o)     , `Assoc(fs)) -> of_json_obj o fs
    | (Obj(_)     , _         ) -> error "expected object value"
  in
  try Ok(of_json s json) with Error(s) -> Error(s)

type params = [`List of json list | `Assoc of (string * json) list] option

let parse_params : type a. _ api -> a Schema.t -> params -> a option =
    fun api s params ->
  let of_json s json =
    match of_json api s json with
    | Ok(v)    -> Some(v)
    | Error(_) -> None
  in
  match (s, params) with
  | (Null  , None               ) -> Some(())
  | (Obj(_), Some(`Assoc(fs)   )) -> of_json s (`Assoc(fs))
  | (_     , Some(`List([json]))) -> of_json s json
  | (_     , _                  ) -> None

let run api ~ic ~oc s =
  let rec loop s =
    match Jsonrpc_tp.recv ~ic () with
    | Error(msg)  -> Error(msg)
    | Ok(None)    -> Ok(s)
    | Ok(Some(p)) ->
    let r = match p with J.Packet.Request(r) -> Some(r) | _ -> None in
    match r with
    | None -> Error("not a request packet")
    | Some(J.Request.{id; method_ = f; params}) ->
    match (f, params) with
    | ("quit", None           ) -> Response.ok ~oc id; Ok(s)
    | ("quit", Some(`List([]))) -> Response.ok ~oc id; Ok(s)
    | ("quit", _              ) -> Response.invalid_params ~oc id f; loop s
    | (_     , _              ) ->
    match SMap.find_opt f api.api_methods with
    | None       -> Response.method_not_found ~oc id f; loop s
    | Some(spec) ->
    match spec with
    | Pure(spec) ->
        begin
          match parse_params api spec.arg params with
          | None         -> Response.invalid_params ~oc id f; loop s
          | Some(params) ->
          let (s, ret) = spec.impl s params in
          let ret = to_json api spec.ret ret in
          let response = J.Response.ok id ret in
          Jsonrpc_tp.send ~oc (J.Packet.Response(response));
          loop s
        end
    | Rslt(spec) ->
        begin
          match parse_params api spec.arg params with
          | None         -> Response.invalid_params ~oc id f; loop s
          | Some(params) ->
          let (s, ret_or_err) = spec.impl s params in
          let response =
            match ret_or_err with
            | Ok(ret)             ->
                let ret = to_json api spec.ret ret in
                J.Response.ok id ret
            | Error(err, message) ->
                let err = to_json api spec.err err in
                let code = J.Response.Error.Code.RequestFailed in
                let err = J.Response.Error.make ~data:err ~code ~message () in
                J.Response.error id err
          in
          Jsonrpc_tp.send ~oc (J.Packet.Response(response));
          loop s
        end
  in
  loop s

let output_docs oc api =
  let line fmt = Printf.fprintf oc (fmt ^^ "\n") in
  let describe_schema s d =
    match d with
    | Some(descr) -> descr ^ " (as " ^ Schema.descr s ^ ")"
    | None        -> Schema.descr s
  in
  let document_object (A(O(o))) =
    line "";
    line "### `%s`" o.name;
    line "";
    Option.iter (line "- Description: %s.") o.descr;
    let rec document_fields : type a. a Fields.t -> unit = fun fields ->
      match fields with Nil -> () | Cns(f) ->
      document_fields f.fields;
      line "- Field `%s`: %s." f.name (describe_schema f.schema f.descr)
    in
    document_fields o.fields
  in
  let document_method name m =
    line "";
    line "### `%s`" name;
    line "";
    match m with
    | Pure(m) ->
        Option.iter (line "- Description: %s.") m.descr;
        line "- Argument: %s." (describe_schema m.arg m.arg_descr);
        line "- Response payload: %s." (describe_schema m.ret m.ret_descr);
        line "- Failure mode: never fails."
    | Rslt(m) ->
        Option.iter (line "- Description: %s.") m.descr;
        line "- Argument: %s." (describe_schema m.arg m.arg_descr);
        line "- Response payload: %s." (describe_schema m.ret m.ret_descr);
        line "- Error payload: %s." (describe_schema m.err m.err_descr);
        line "- Failure mode: %srecoverable failure."
          (if m.recoverable then "" else "un");
  in
  if api.api_objects <> [] then begin
    line "API Objects";
    line "-----------";
    List.iter document_object (List.rev api.api_objects);
    line "";
  end;
  line "API Methods";
  line "------------";
  SMap.iter document_method api.api_methods

let output_python_api oc api =
  ignore (oc, api);
  Printf.eprintf "Error: not implemented.\n%!"; exit 1


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

  let rec python : type a. a t -> string = fun s ->
    match s with
    | Null -> "None"
    | Any -> "Any"
    | Int -> "int"
    | Bool -> "bool"
    | String -> "str"
    | Nullable s -> python s ^ " | None"
    | List s -> "list[" ^ python s ^ "]"
    | Obj o -> o

  let is_default : type a. a t -> a -> bool = fun s v ->
    match (s, v) with
    | (Null       , ()   ) -> true
    | (Bool       , false) -> true
    | (List(_)    , []   ) -> true
    | (Nullable(_), None ) -> true
    | (_          , _    ) -> false

  let default : type a. a t -> a option = fun s ->
    match s with
    | Null        -> Some(())
    | Bool        -> Some(false)
    | List(_)     -> Some([])
    | Nullable(_) -> Some(None)
    | _           -> None
end

module GenList() = struct
  type _ t =
    | Nil : unit t
    | Cns : {
        name : string;
        descr : string option;
        schema : 'a Schema.t;
        tail : 'b t
      } -> ('a * 'b) t

  let nil = Nil
  let add ~name ?descr schema tail =
    Cns({name; descr; schema; tail})
end

module Fields = GenList()
module Args = GenList()

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

type ('s, 'a, 'b) api_method_impl =
  | Pure : {
      impl : ('s -> 'a -> 's * 'b);
    } -> ('s, 'a, 'b) api_method_impl
  | Rslt : {
      err : 'e Schema.t;
      err_descr : string option;
      recoverable : bool;
      impl : ('s -> 'a -> 's * ('b, 'e * string) Result.t);
    } -> ('s, 'a, 'b) api_method_impl

type 's api_method = M : {
  name : string;
  descr : string option;
  args : 'a Args.t;
  ret : 'b Schema.t;
  ret_descr : string option;
  impl : ('s, 'a, 'b) api_method_impl;
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

let declare api ~name ?descr ~args ~ret ?ret_descr impl =
  match SMap.mem name api.api_methods with
  | true  -> duplicate "declare"
  | false ->
  let m = M({name; descr; args; ret; ret_descr; impl = Pure({impl})}) in
  api.api_methods <- SMap.add name m (api.api_methods)

let declare_full api ~name ?descr ~args ~ret ?ret_descr
    ~err ?err_descr ?(recoverable=true) impl =
  match SMap.mem name api.api_methods with
  | true  -> duplicate "declare_full"
  | false ->
  let impl = Rslt({err; err_descr; recoverable; impl}) in
  let m = M({name; descr; args; ret; ret_descr; impl}) in
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
    | (Nil                            , ()     ) -> []
    | (Cns({name; schema; tail=fs; _}), (v, vs)) ->
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
        | Nil                             -> ()
        | Cns({name; schema; tail=fs; _}) ->
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

let parse_params : type a. _ api -> a Args.t -> params -> a option =
    fun api args params ->
  let rec parse_list : type a. a Args.t -> json list -> a option =
      fun args js ->
    match (args, js) with
    | (Args.Nil   , []     ) -> Some(())
    | (Args.Nil   , _ :: _ ) -> None
    | (Args.Cns(_), []     ) -> None
    | (Args.Cns(a), j :: js) ->
    match of_json api a.schema j with
    | Error(_) -> None
    | Ok(v)    ->
    match parse_list a.tail js with
    | None     -> None
    | Some(vs) -> Some((v, vs))
  in
  let rec parse_assoc : type a. a Args.t -> (string * json) list -> a option =
      fun args fs ->
    match (args, fs) with
    | (Args.Nil   , []) -> Some(())
    | (Args.Nil   , _ ) -> None
    | (Args.Cns(_), []) -> None
    | (Args.Cns(a), _ ) ->
    match List.assoc_opt a.name fs with
    | None    -> None
    | Some(j) ->
    match of_json api a.schema j with
    | Error(_) -> None
    | Ok(v)    ->
    let fs = List.remove_assoc a.name fs in
    match parse_assoc a.tail fs with
    | None     -> None
    | Some(vs) -> Some((v, vs))
  in
  match (args, params) with
  | (Args.Nil   , None            ) -> Some(())
  | (Args.Nil   , Some(`List([])) ) -> Some(())
  | (Args.Nil   , Some(`Assoc([]))) -> Some(())
  | (Args.Nil   , Some(_)         ) -> None
  | (Args.Cns(_), None            ) -> None
  | (Args.Cns(_), Some(`List(ls)) ) -> parse_list args ls
  | (Args.Cns(_), Some(`Assoc(fs))) -> parse_assoc args fs

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
    | None          -> Response.method_not_found ~oc id f; loop s
    | Some(M(spec)) ->
    match parse_params api spec.args params with
    | None         -> Response.invalid_params ~oc id f; loop s
    | Some(params) ->
    let s =
      match spec.impl with
      | Pure(impl) ->
          begin
            match impl.impl s params with
            | exception Invalid_argument(msg) ->
                Response.invalid_params ~oc id ~msg f; s
            | (s, ret)                        ->
            let ret = to_json api spec.ret ret in
            let response = J.Response.ok id ret in
            Jsonrpc_tp.send ~oc (J.Packet.Response(response)); s
          end
      | Rslt(impl) ->
          begin
            match impl.impl s params with
            | exception Invalid_argument(msg) ->
                Response.invalid_params ~oc id ~msg f; s
            | (s, ret_or_err)                 ->
            let response =
              match ret_or_err with
              | Ok(ret)             ->
                  let ret = to_json api spec.ret ret in
                  J.Response.ok id ret
              | Error(err, message) ->
                  let data =
                    match impl.err with
                    | Null -> None
                    | _    -> Some(to_json api impl.err err)
                  in
                  let code = J.Response.Error.Code.RequestFailed in
                  let err = J.Response.Error.make ?data ~code ~message () in
                  J.Response.error id err
            in
            Jsonrpc_tp.send ~oc (J.Packet.Response(response)); s
          end
    in
    loop s
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
      document_fields f.tail;
      line "- Field `%s`: %s." f.name (describe_schema f.schema f.descr)
    in
    document_fields o.fields
  in
  let document_method name (M(m)) =
    line "";
    line "### `%s`" name;
    line "";
    Option.iter (line "- Description: %s.") m.descr;
    begin
      match m.args with Args.Nil -> () | _ ->
      line "- Arguments (in order, or named):";
      let rec print_args : type a. a Args.t -> unit = fun args ->
        match args with
        | Args.Nil    -> ()
        | Args.Cns(a) ->
        line "  - %s: %s." a.name (describe_schema a.schema a.descr);
        print_args a.tail
      in
      print_args m.args
    end;
    line "- Response payload: %s." (describe_schema m.ret m.ret_descr);
    match m.impl with
    | Pure(_) ->
        line "- Failure mode: never fails."
    | Rslt(m) ->
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
  let line fmt = Printf.fprintf oc (fmt ^^ "\n") in
  line "from dataclasses import dataclass";
  line "from typing import Any, cast";
  line "";
  line "from .rocq_doc_manager_raw import Err, RocqDocManagerRaw";
  line "";
  let output_object (A(O(o))) =
    line "";
    Option.iter (line "# Description: %s.") o.descr;
    line "@dataclass";
    line "class %s:" o.name;
    let rec output_fields : type a. a Fields.t -> unit = fun fields ->
      match fields with Nil -> () | Cns(f) ->
      output_fields f.tail;
      Option.iter (line "    # Description: %s.") f.descr;
      line "    %s: %s" f.name (Schema.python f.schema)
    in
    output_fields o.fields
  in
  List.iter output_object (List.rev api.api_objects);
  line "";
  line "class RocqDocManagerAPI(RocqDocManagerRaw):";
  let rec pp_args : type a. _ -> a Args.t -> unit = fun oc args ->
    match args with
    | Args.Nil    -> ()
    | Args.Cns(a) ->
    Printf.fprintf oc ", %s: %s" a.name (Schema.python a.schema);
    pp_args oc a.tail
  in
  let rec pp_names : type a. _ -> a Args.t -> unit = fun oc args ->
    match args with
    | Args.Nil    -> ()
    | Args.Cns(a) ->
    let comma = match a.tail with Args.Nil -> "" | _ -> ", " in
    Printf.fprintf oc "%s%s" a.name comma;
    pp_names oc a.tail
  in
  let output_method _ (M(m)) =
    line "";
    Option.iter (line "    # Description: %s.") m.descr;
    let ret_ty =
      match m.impl with
      | Pure(_) -> Schema.python m.ret
      | Rslt(i) -> Schema.python m.ret ^ " | Err[" ^ Schema.python i.err ^ "]"
    in
    line "    def %s(self%a) -> %s:" m.name pp_args m.args ret_ty;
    line "        result = self.request(\"%s\", [%a])" m.name pp_names m.args;
    let _ =
      match m.impl with Pure(_) -> () | Rslt(i) ->
      line "        if isinstance(result, Err):";
      line "            data = cast(%s, result.data)" (Schema.python i.err);
      line "            return Err(result.message, data)"
    in
    line "        return cast(%s, result)" (Schema.python m.ret)
  in
  SMap.iter output_method api.api_methods

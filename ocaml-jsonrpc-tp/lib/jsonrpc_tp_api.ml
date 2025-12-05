type 'a api_obj = {name : string; default : 'a option}

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
    | Obj o -> "an instance of the `" ^ o.name ^ "` object"

  let python_type : type a. cls:string -> a t -> string = fun ~cls ->
    let rec python_type : type a. a t -> string = function
      | Null -> "None"
      | Any -> "Any"
      | Int -> "int"
      | Bool -> "bool"
      | String -> "str"
      | Nullable s -> python_type s ^ " | None"
      | List s -> "list[" ^ python_type s ^ "]"
      | Obj o -> Printf.sprintf "%s.%s" cls o.name
    in
    python_type

  (* Ensure every field has a default; auto-generated methods use dictionary
     unpacking and must handle cases where null/empty fields are elided. *)
  let python_dataclass_field : type a. cls:string -> a t -> string =
      fun ~cls s ->
    Printf.sprintf "field(kw_only=True, %s)" @@
    match s with
    | Null -> "default=None"
    | Any -> "default=None"
    | Int -> "default=0"
    | Bool -> "default=False"
    | String -> "default=\"\""
    | Nullable _ -> "default=None"
    | List _ -> "default_factory=list"
    | Obj o -> Printf.sprintf "default_factory=lambda: %s.%s()" cls o.name

  let python_val : type a. string -> a t -> string = fun var s ->
    let fresh = let c = ref 0 in fun () -> incr c; Printf.sprintf "v%i" !c in
    let rec python_val : type a. string -> a t -> string = fun var s ->
      match s with
      | Null -> "None"
      | Any -> var
      | Int -> Printf.sprintf "int(%s)" var
      | Bool -> Printf.sprintf "bool(%s)" var
      | String -> Printf.sprintf "str(%s)" var
      | Nullable s ->
          Printf.sprintf "None if %s is None else %s" var (python_val var s)
      | List s ->
          let fresh = fresh () in
          Printf.sprintf "[%s for %s in %s]" (python_val fresh s) fresh var
      | Obj o -> Printf.sprintf "self.%s.from_dict(%s)" o.name var
    in
    python_val var s

  let is_default : type a. a t -> a -> bool = fun s v ->
    match (s, v) with
    | (Null       , ()   ) -> true
    | (Bool       , false) -> true
    | (List(_)    , []   ) -> true
    | (Nullable(_), None ) -> true
    | (Obj(o)     , v    ) -> Some(v) = o.default
    | (_          , _    ) -> false

  let default : type a. a t -> a option = fun s ->
    match s with
    | Null        -> Some(())
    | Bool        -> Some(false)
    | List(_)     -> Some([])
    | Nullable(_) -> Some(None)
    | Obj(o)      -> o.default
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
      key : 'b api_obj;
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
      impl : ('s -> 'a -> 's * ('b, string * 'e) Result.t);
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
  name : string;
  mutable api_objects : any_obj list;
  mutable api_methods : 's api_method SMap.t;
}

let get_obj : type a. _ api -> a api_obj -> a obj = fun api k ->
  match List.find_opt (fun (A(O(o))) -> o.key.name = k.name) api.api_objects with
  | None       -> assert false
  | Some(A(o)) -> Obj.magic o

let create : name:string -> _ api = fun ~name ->
  {name; api_objects = []; api_methods = SMap.empty}

let duplicate fname =
  raise (Invalid_argument("Jsonrpc_tp_api." ^ fname ^ ": duplicate name"))

let declare_object api ~name ?descr ?default ~encode ~decode fields =
  match List.exists (fun (A(O(r))) -> r.key.name = name) api.api_objects with
  | true  -> duplicate "declare_object"
  | false ->
  let key = {name; default} in
  let o = A(O({key; descr; fields; encode; decode})) in
  api.api_objects <- o :: api.api_objects; key

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

type context =
  | Field of {name : string; field : string}
  | ListItem of int
  | NullableItem

let add_context : context list -> string -> string = fun ctxt s ->
  let add s item =
    match item with
    | Field(f)     ->
        Printf.sprintf "in field %s of class %s, %s" f.field f.name s
    | ListItem(i)  ->
        Printf.sprintf "in item %i of the list, %s" i s
    | NullableItem ->
        Printf.sprintf "in a non-null value, %s" s
  in
  List.fold_left add s ctxt

let of_json : type a. _ api -> a Schema.t -> json -> (a, string) Result.t =
    fun api s json ->
  let exception Error of context list * string in
  let error ctxt s = raise (Error(ctxt, s)) in
  let rec of_json : type a. context list -> a Schema.t -> json -> a =
      fun ctxt s json ->
    let of_json_obj : type a. context list -> a api_obj -> (string * json) list -> a = fun ctxt o fields ->
      let O(o) = get_obj api o in
      let rec make : type a. a Fields.t -> a = fun fs ->
        let open Fields in
        match fs with
        | Nil                             -> ()
        | Cns({name; schema; tail=fs; _}) ->
        match List.assoc_opt name fields with
        | Some(json) ->
            let ctxt = Field({name=o.key.name; field=name}) :: ctxt in
            (of_json ctxt schema json, make fs)
        | None       ->
        match Schema.default schema with
        | Some(v)    -> (v, make fs)
        | None       -> error ctxt ("missing object field \"" ^ name ^ "\"")
      in
      o.encode (make o.fields)
    in
    match (s, json) with
    | (Null       , `Null     ) -> ()
    | (Null       , _         ) -> error ctxt "expected null value"
    | (Any        , _         ) -> json
    | (Int        , `Int(i)   ) -> i
    | (Int        , _         ) -> error ctxt "expected integer value"
    | (Bool       , `Bool(b)  ) -> b
    | (Bool       , _         ) -> error ctxt "expected boolean value"
    | (String     , `String(s)) -> s
    | (String     , _         ) -> error ctxt "expected string value"
    | (Nullable(_), `Null     ) -> None
    | (Nullable(s), _         ) ->
        Some(of_json (NullableItem :: ctxt) s json)
    | (List(s)    , `List(vs) ) ->
        List.mapi (fun i v -> of_json (ListItem(i) :: ctxt) s v) vs
    | (List(_)    , _         ) -> error ctxt "expected list value"
    | (Obj(o)     , `Assoc(fs)) ->
        of_json_obj ctxt o fs
    | (Obj(_)     , _         ) -> error ctxt "expected object value"
  in
  try Ok(of_json [] s json) with Error(ctxt, s) -> Error(add_context ctxt s)

type params = [`List of json list | `Assoc of (string * json) list] option

let parse_params : type a. _ api -> a Args.t -> params -> (a, string) result =
    fun api args params ->
  let rec parse_list : type a. a Args.t -> json list -> (a, string) result =
      fun args js ->
    match (args, js) with
    | (Args.Nil   , []     ) -> Ok(())
    | (Args.Nil   , _ :: _ ) -> Error("Too many arguments.")
    | (Args.Cns(a), []     ) -> Error("Missing argument '" ^ a.name ^ "'.")
    | (Args.Cns(a), j :: js) ->
    match of_json api a.schema j with
    | Error(s) -> Error("Ill-typed argument '" ^ a.name ^ "': " ^ s)
    | Ok(v)    ->
    match parse_list a.tail js with
    | Error(s) -> Error(s)
    | Ok(vs)   -> Ok((v, vs))
  in
  let rec parse_assoc : type a. a Args.t -> (string * json) list
      -> (a, string) result = fun args fs ->
    match (args, fs) with
    | (Args.Nil   , []) -> Ok(())
    | (Args.Nil   , _ ) -> Error("Too many arguments.")
    | (Args.Cns(a), _ ) ->
    match List.assoc_opt a.name fs with
    | None    -> Error("Missing argument '" ^ a.name ^ "'.")
    | Some(j) ->
    match of_json api a.schema j with
    | Error(s) -> Error("Ill-typed argument '" ^ a.name ^ "': " ^ s)
    | Ok(v)    ->
    let fs = List.remove_assoc a.name fs in
    match parse_assoc a.tail fs with
    | Error(s) -> Error(s)
    | Ok(vs)   -> Ok((v, vs))
  in
  match (args, params) with
  | (Args.Nil   , None            ) -> Ok(())
  | (Args.Nil   , Some(`List([])) ) -> Ok(())
  | (Args.Nil   , Some(`Assoc([]))) -> Ok(())
  | (Args.Nil   , Some(_)         ) -> Error("No arguments expected.")
  | (Args.Cns(_), None            ) -> Error("Arguments expected.")
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
    | Error(msg) -> Response.invalid_params ~oc id ~msg f; loop s
    | Ok(params) ->
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
              | Error(message, err) ->
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
    line "### `%s`" o.key.name;
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
  let pp_capitalized oc s = output_string oc (String.capitalize_ascii s) in
  line "from __future__ import annotations";
  line "";
  line "# ruff: noqa: C416 -- unnecessary list comprehension";
  line "from dataclasses import dataclass, field";
  line "from typing import Any, TypeAlias";
  line "";
  line "from dataclasses_json import DataClassJsonMixin";
  line "from jsonrpc_tp import JsonRPCTP";
  line "";
  line "";
  line "class %s:" api.name;
  line "    \"\"\"Main API class.\"\"\"";
  line "";
  line "    Err: TypeAlias = JsonRPCTP.Err # noqa: UP040";
  line "    Resp: TypeAlias = JsonRPCTP.Resp # noqa: UP040";
  line "    Error: TypeAlias = JsonRPCTP.Error # noqa: UP040";
  line "";
  line "    def __init__(self, rpc: JsonRPCTP) -> None:";
  line "        self._rpc:JsonRPCTP = rpc";
  let output_object (A(O(o))) =
    line "";
    line "    @dataclass";
    line "    class %s(DataClassJsonMixin):" o.key.name;
    Option.iter (line "        \"\"\"%a.\"\"\"" pp_capitalized) o.descr;
    let rec output_fields : type a. a Fields.t -> unit = fun fields ->
      match fields with Nil -> () | Cns(f) ->
      output_fields f.tail;
      Option.iter (line "        # %a." pp_capitalized) f.descr;
      line "        %s: %s = %s" f.name
        (Schema.python_type ~cls:api.name f.schema)
        (Schema.python_dataclass_field ~cls:api.name f.schema)
    in
    output_fields o.fields
  in
  List.iter output_object (List.rev api.api_objects);
  let rec pp_args : type a. _ -> a Args.t -> unit = fun oc args ->
    match args with
    | Args.Nil    -> ()
    | Args.Cns(a) ->
    Printf.fprintf oc ", %s: %s" a.name
      (Schema.python_type ~cls:api.name a.schema);
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
    let ret_ty =
      match m.impl with
      | Pure(_) -> Schema.python_type ~cls:api.name m.ret
      | Rslt(i) ->
          let ret = Schema.python_type ~cls:api.name m.ret in
          let err = Schema.python_type ~cls:api.name i.err in
          Printf.sprintf "%s | %s.Err[%s]" ret api.name err
    in
    line "    def %s(self%a) -> %s:" m.name pp_args m.args ret_ty;
    Option.iter (line "        \"\"\"%a.\"\"\"" pp_capitalized) m.descr;
    line "        result = self._rpc.raw_request(\"%s\", [%a])"
      m.name pp_names m.args;
    let _ =
      (* We check the result against [JsonRPCTP.Err] rather than [self.Err]
         to decouple these *)
      match m.impl with
      | Pure(_) ->
        line "        assert not isinstance(result, JsonRPCTP.Err)";
      | Rslt(i) ->
        line "        if isinstance(result, JsonRPCTP.Err):";
        line "            data = %s" (Schema.python_val "result.data" i.err);
        line "            return %s.Err(result.message, data)" api.name
    in
    line "        return %s" (Schema.python_val "result.result" m.ret)
  in
  SMap.iter output_method api.api_methods

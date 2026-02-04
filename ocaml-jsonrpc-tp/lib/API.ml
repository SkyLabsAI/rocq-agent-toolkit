type 'a api_obj = {name : string; default : 'a option}

type json = Yojson.Safe.t

module Schema = struct
  type 'a variant_spec = {
    values : 'a list;
    default : 'a;
    encode : 'a -> string;
  }

  type _ t =
    | Null : unit t
    | Any : json t
    | Int : int t
    | Bool : bool t
    | String : string t
    | Variant : 'a variant_spec -> 'a t
    | Nullable : 'a t -> 'a option t
    | List : 'a t -> 'a list t
    | Obj : 'a api_obj -> 'a t

  let null = Null
  let any = Any
  let int = Int
  let bool = Bool
  let string = String
  let variant ~values ~default ~encode = Variant({values; default; encode})
  let nullable s = Nullable(s)
  let list s = List(s)
  let obj o = Obj(o)

  let descr_variant : 'a variant_spec -> string = fun s ->
    let to_string v = Printf.sprintf "`%S`" (s.encode v) in
    String.concat ", " (List.map to_string s.values)

  let rec descr : type a. a t -> string = fun s ->
    match s with
    | Null -> "a `null` value"
    | Any -> "a JSON value"
    | Int -> "an integer"
    | Bool -> "a boolean"
    | String -> "a string"
    | Variant s -> "any of " ^ descr_variant s
    | Nullable s -> "either `null` or " ^ descr s
    | List s -> "a list where each element is " ^ descr s
    | Obj o -> "an instance of the `" ^ o.name ^ "` object"

  let python_type_variant : 'a variant_spec -> string = fun s ->
    let to_string v = Printf.sprintf "%S" (s.encode v) in
    "Literal[" ^ String.concat ", " (List.map to_string s.values) ^ "]"

  let python_type : type a. a t -> string =
    let rec python_type : type a. a t -> string = function
      | Null -> "None"
      | Any -> "Any"
      | Int -> "int"
      | Bool -> "bool"
      | String -> "str"
      | Variant s -> python_type_variant s
      | Nullable s -> python_type s ^ " | None"
      | List s -> "list[" ^ python_type s ^ "]"
      | Obj o -> Printf.sprintf "%s" o.name
    in
    python_type

  (* Ensure every field has a default; auto-generated methods use dictionary
     unpacking and must handle cases where null/empty fields are elided. *)
  let python_dataclass_field : type a. a t -> string = fun s ->
    Printf.sprintf "field(kw_only=True, %s)" @@
    match s with
    | Null -> "default=None"
    | Any -> "default=None"
    | Int -> "default=0"
    | Bool -> "default=False"
    | String -> "default=\"\""
    | Variant s -> Printf.sprintf "default=%S" (s.encode s.default)
    | Nullable _ -> "default=None"
    | List _ -> "default_factory=list"
    | Obj o -> Printf.sprintf "default_factory=lambda: %s()" o.name

  let python_val : type a. string -> a t -> string = fun var s ->
    let fresh = let c = ref 0 in fun () -> incr c; Printf.sprintf "v%i" !c in
    let rec python_val : type a. string -> a t -> string = fun var s ->
      match s with
      | Null -> "None"
      | Any -> var
      | Int -> Printf.sprintf "int(%s)" var
      | Bool -> Printf.sprintf "bool(%s)" var
      | String -> Printf.sprintf "str(%s)" var
      | Variant _ -> Printf.sprintf "str(%s)" var
      | Nullable s ->
          Printf.sprintf "None if %s is None else %s" var (python_val var s)
      | List s ->
          let fresh = fresh () in
          Printf.sprintf "[%s for %s in %s]" (python_val fresh s) fresh var
      | Obj o -> Printf.sprintf "%s.from_dict(%s)" o.name var
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

type 'a emitted_notification = {
  name : string;
  descr : string option;
  args : 'a Args.t;
}

type any_emitted_notification =
  | AEN : 'a emitted_notification -> any_emitted_notification
[@@unboxed]

type notification = N : 'a emitted_notification * 'a -> notification

module SMap = Map.Make(String)

type ('s, 'a, 'b) api_method_impl =
  | Pure : {
      impl : ((notification -> unit) -> 's -> 'a -> 'b);
    } -> ('s, 'a, 'b) api_method_impl
  | Rslt : {
      err : 'e Schema.t;
      err_descr : string option;
      recoverable : bool;
      impl : ((notification -> unit) -> 's -> 'a -> ('b, string * 'e) Result.t);
    } -> ('s, 'a, 'b) api_method_impl

type 's api_method = M : {
  name : string;
  descr : string option;
  args : 'a Args.t;
  ret : 'b Schema.t;
  ret_descr : string option;
  impl : ('s, 'a, 'b) api_method_impl;
} -> 's api_method

type handled_notification = HN : {
  name : string;
  descr : string option;
  args : 'a Args.t;
  impl : ((notification -> unit) -> 'a -> unit);
} -> handled_notification

type 's api = {
  name : string;
  mutable api_objects : any_obj list;
  mutable api_methods : 's api_method SMap.t;
  mutable api_hd_notifs : handled_notification SMap.t;
  mutable api_em_notifs : any_emitted_notification SMap.t;
}

let get_obj : type a. _ api -> a api_obj -> a obj = fun api k ->
  match List.find_opt (fun (A(O(o))) -> o.key.name = k.name) api.api_objects with
  | None       -> assert false
  | Some(A(o)) -> Obj.magic o

let create : name:string -> _ api = fun ~name ->
  let api_objects = [] in
  let api_methods = SMap.empty in
  let api_hd_notifs = SMap.empty in
  let api_em_notifs = SMap.empty in
  {name; api_objects; api_methods; api_hd_notifs; api_em_notifs}

let duplicate fname =
  invalid_arg ("Jsonrpc_tp.Interface." ^ fname ^ ": duplicate name")

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

let declare_handled_notification api ~name ?descr ~args impl =
  match SMap.mem name api.api_hd_notifs with
  | true  -> duplicate "declare_handled_notification"
  | false ->
  let hn = HN({name; descr; args; impl}) in
  api.api_hd_notifs <- SMap.add name hn api.api_hd_notifs

let declare_emittable_notification api ~name ?descr ~args =
  match SMap.mem name api.api_em_notifs with
  | true  -> duplicate "declare_emittable_notification"
  | false ->
  let en = {name; descr; args} in
  api.api_em_notifs <- SMap.add name (AEN(en)) api.api_em_notifs;
  fun v -> N(en, v)

let rec to_json : type a. _ api -> a Schema.t -> a -> json = fun api s v ->
  match (s, v) with
  | (Null       , ()     ) -> `Null
  | (Any        , _      ) -> v
  | (Int        , _      ) -> `Int(v)
  | (Bool       , _      ) -> `Bool(v)
  | (String     , _      ) -> `String(v)
  | (Variant(s) , v      ) -> `String(s.encode v)
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
    let of_json_obj : type a. context list -> a api_obj ->
        (string * json) list -> a = fun ctxt o fields ->
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
    | (Variant(r) , `String(s)) ->
        begin
          match List.find_opt (fun v -> r.encode v = s) r.values with
          | None    -> error ctxt "unknown variant"
          | Some(v) -> v
        end
    | (Variant(_) , _         ) -> error ctxt "expected string value"
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

let make_params : type a. _ api -> a Args.t -> a -> params = fun api args v ->
  let rec make : type a. (string * json) list -> a Args.t -> a -> params =
      fun fs args v ->
    match (args, v) with
    | (Args.Nil   , ()     ) -> Some(`Assoc(fs))
    | (Args.Cns(a), (v, vs)) ->
    make ((a.name, to_json api a.schema v) :: fs) a.tail vs
  in
  match args with
  | Args.Nil -> None
  | _        -> make [] args v

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

let handle_request : type s. s api -> s -> Service.request_handler =
    fun api s ~name ~params ~notify ->
  let invalid_params ?msg name =
    let msg =
      let msg = match msg with None -> "" | Some(msg) -> ": " ^ msg in
      Printf.sprintf "Invalid parameters for method %s%s." name msg
    in
    Service.Response.(error ~code:InvalidParams msg)
  in
  let notify (N({name; args; _}, v)) =
    notify ~name ~params:(make_params api args v)
  in
  match SMap.find_opt name api.api_methods with
  | None          ->
      let msg = Printf.sprintf "Method %s not found." name in
      Service.Response.(error ~code:MethodNotFound msg)
  | Some(M(spec)) ->
  match parse_params api spec.args params with
  | Error(msg) -> invalid_params ~msg name
  | Ok(params) ->
  match spec.impl with
  | Pure(impl) ->
      begin
        match impl.impl notify s params with
        | exception Invalid_argument(msg) -> invalid_params ~msg name
        | ret                             ->
        let json = to_json api spec.ret ret in
        Service.Response.ok json
      end
  | Rslt(impl) ->
      begin
        match impl.impl notify s params with
        | exception Invalid_argument(msg) -> invalid_params ~msg name
        | Ok(ret)             ->
            let json = to_json api spec.ret ret in
            Service.Response.ok json
        | Error(message, err) ->
            let data =
              match impl.err with
              | Null -> None
              | _    -> Some(to_json api impl.err err)
            in
            Service.Response.(error ~code:RequestFailed ?data message)
      end

let handle_notification ~name:_ ~params:_ ~notify:_ = ()

let notify_ready ~oc ~sequential =
  let method_ = if sequential then "ready_seq" else "ready" in
  let notification = Jsonrpc.Notification.create ~method_ () in
  Base.send ~oc (Jsonrpc.Packet.Notification(notification))

let run_seq api ~ic ~oc s =
  let handle_request = handle_request api s in
  notify_ready ~oc ~sequential:true;
  Service.run_seq ~ic ~oc ~handle_request ~handle_notification

let run api ~ic ~oc ~workers s =
  let handle_request = handle_request api s in
  notify_ready ~oc ~sequential:false;
  Service.run ~ic ~oc ~workers ~handle_request ~handle_notification

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
        line "  - `%s`: %s." a.name (describe_schema a.schema a.descr);
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
  let document_notif (type a) emitted name descr (args : a Args.t) =
    line "";
    line "### `%s`" name;
    line "";
    Option.iter (line "- Description: %s.") descr;
    begin
      match args with Args.Nil -> () | _ ->
      line "- Arguments (%snamed):" (if emitted then "" else "in order, or ");
      let rec print_args : type a. a Args.t -> unit = fun args ->
        match args with
        | Args.Nil    -> ()
        | Args.Cns(a) ->
        line "  - `%s`: %s." a.name (describe_schema a.schema a.descr);
        print_args a.tail
      in
      print_args args
    end
  in
  let document_hd_notif name (HN({descr; args; _})) =
    document_notif false name descr args
  in
  let document_em_notif name (AEN({descr; args; _})) =
    document_notif true name descr args
  in
  if api.api_objects <> [] then begin
    line "API Objects";
    line "-----------";
    List.iter document_object (List.rev api.api_objects);
    line "";
  end;
  line "API Methods";
  line "------------";
  SMap.iter document_method api.api_methods;
  if api.api_hd_notifs <> SMap.empty then begin
    line "";
    line "API Handled Notifications";
    line "------------";
    SMap.iter document_hd_notif api.api_hd_notifs
  end;
  if api.api_em_notifs <> SMap.empty then begin
    line "";
    line "API Emitted Notifications";
    line "------------";
    SMap.iter document_em_notif api.api_em_notifs
  end

let output_python_api oc api =
  let line fmt = Printf.fprintf oc (fmt ^^ "\n") in
  let pp_capitalized oc s = output_string oc (String.capitalize_ascii s) in
  line "from __future__ import annotations";
  line "";
  line "from dataclasses import dataclass, field";
  line "";
  line "# ruff: noqa: C416 -- unnecessary list comprehension";
  line "from typing import Any, Literal";
  line "";
  line "from dataclasses_json import DataClassJsonMixin";
  line "from jsonrpc_tp import Err, Error, JsonRPCTP, Resp";
  line "";
  let exports =
    [api.name; "Err"; "Error"; "Resp"] @
    List.map (fun (A(O(o))) -> o.key.name) api.api_objects
  in
  line "__all__ = [";
  List.iter (line "  '%s',") exports;
  line "]";
  let output_object (A(O(o))) =
    line "";
    line "@dataclass(frozen=True)";
    line "class %s(DataClassJsonMixin):" o.key.name;
    Option.iter (line "    \"\"\"%a.\"\"\"" pp_capitalized) o.descr;
    let rec output_fields : type a. a Fields.t -> unit = fun fields ->
      match fields with Nil -> () | Cns(f) ->
      output_fields f.tail;
      Option.iter (line "   # %a." pp_capitalized) f.descr;
      line "    %s: %s = %s" f.name
        (Schema.python_type f.schema)
        (Schema.python_dataclass_field f.schema)
    in
    output_fields o.fields
  in
  List.iter output_object (List.rev api.api_objects);
  line "";
  line "class %s:" api.name;
  line "    \"\"\"Main API class.\"\"\"";
  line "";
  line "    def __init__(self, rpc: JsonRPCTP) -> None:";
  line "        self._rpc:JsonRPCTP = rpc";
  let rec pp_args : type a. _ -> a Args.t -> unit = fun oc args ->
    match args with
    | Args.Nil    -> ()
    | Args.Cns(a) ->
    Printf.fprintf oc ", %s: %s" a.name
      (Schema.python_type a.schema);
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
      | Pure(_) -> Schema.python_type m.ret
      | Rslt(i) ->
          let ret = Schema.python_type m.ret in
          let err = Schema.python_type i.err in
          Printf.sprintf "%s | Err[%s]" ret err
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
        line "        assert not isinstance(result, Err)";
      | Rslt(i) ->
        line "        if isinstance(result, Err):";
        line "            data = %s" (Schema.python_val "result.data" i.err);
        line "            return Err(result.message, data)"
    in
    line "        return %s" (Schema.python_val "result.result" m.ret)
  in
  SMap.iter output_method api.api_methods;
  let output_notification _ (HN(n)) =
    line "";
    line "    def %s(self%a) -> None:" n.name pp_args n.args;
    Option.iter (line "        \"\"\"%a.\"\"\"" pp_capitalized) n.descr;
    line "        self._rpc.raw_notification(\"%s\", [%a])"
      n.name pp_names n.args
  in
  SMap.iter output_notification api.api_hd_notifs

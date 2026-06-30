(* We track mutual inductives in a [Mindmap_env] used as a set (the [_env]
   variant; [Names.Mindset] is deprecated). *)
type t = Names.Cset.t * unit Names.Mindmap_env.t

(* The mutual-inductive names collected in [inds], as a list. *)
let minds_of (inds : unit Names.Mindmap_env.t) : Names.MutInd.t list =
  List.rev (Names.Mindmap_env.fold (fun k _ acc -> k :: acc) inds [])

let term_deps : Constr.named_context -> Constr.t -> t = fun hyps t ->
  let constants = ref Names.Cset.empty in
  let inductives = ref Names.Mindmap_env.empty in
  let rec term_deps t =
    let _ =
      match Constr.kind t with
      | Constr.Const((c,_))     ->
          constants := Names.Cset.add c !constants
      | Constr.Ind((i,_))       ->
          inductives := Names.Mindmap_env.add (fst i) () !inductives
      | Constr.Construct((c,_)) ->
          inductives := Names.Mindmap_env.add (fst (fst c)) () !inductives
      | _                       ->
          ()
    in
    Constr.iter term_deps t
  in
  List.iter (Context.Named.Declaration.iter_constr term_deps) hyps;
  term_deps t;
  (!constants, !inductives)

(* The (inductive names, constant names) of a collected [t]. Shared by the
   [DepsOfJSON] command and the [term_deps] Ltac2 external. *)
let dep_names ((constants, inductives) : t) : string list * string list =
  (List.map Names.MutInd.to_string (minds_of inductives),
   List.map Names.Constant.to_string (Names.Cset.elements constants))

let constant_of_qualid : Libnames.qualid -> Names.Constant.t = fun r ->
  let error pp = CErrors.user_err ?loc:r.CAst.loc pp in
  let open Names.GlobRef in
  let error kind =
    let prefix = "This reference is not a constant, but " in
    error Pp.(str prefix ++ str kind ++ str ".")
  in
  match Nametab.global r with
  | ConstRef(c)     -> c
  | VarRef(_)       -> error "a variable"
  | IndRef(_)       -> error "an inductive"
  | ConstructRef(_) -> error "a constructor"

let print_term_deps : Libnames.qualid -> unit = fun r ->
  let error pp = CErrors.user_err ?loc:r.CAst.loc pp in
  let c = constant_of_qualid r in
  let (hyps, t) =
    let c = Global.lookup_constant c in
    let open Declarations in
    let error msg =
      error Pp.(str "This constant is " ++ str msg ++ str ".")
    in
    match c.const_body with
    | Undef(_)     -> error "undefined"
    | Def(t)       -> (c.const_hyps, t)
    | OpaqueDef(_) -> error "opaque"
    | Primitive(_) -> error "a primitive"
    | Symbol(_)    -> error "a symbol"
  in
  let (constants, inductives) = term_deps hyps t in
  let constants = Names.Cset.elements constants in
  let inductives = minds_of inductives in
  let pp_c c = Pp.(str "- " ++ Names.Constant.print c ++ fnl ()) in
  let pp_i i = Pp.(str "- " ++ Names.MutInd.print i ++ fnl ()) in
  let pp =
    let open Pp in
    str "Constants:" ++ fnl () ++ seq (List.map pp_c constants) ++
    str "Inductives:" ++ fnl () ++ seq (List.map pp_i inductives)
  in
  Feedback.msg_notice pp

let print_json_term_deps : Libnames.qualid -> unit = fun r ->
  let c = constant_of_qualid r in
  let (kind, hyps, def) =
    let c = Global.lookup_constant c in
    let hyps = c.const_hyps in
    match c.const_body with
    | Declarations.Undef(_)     -> ("Undef"    , hyps, None   )
    | Declarations.Def(t)       -> ("Def"      , hyps, Some(t))
    | Declarations.OpaqueDef(_) -> ("OpaqueDef", hyps, None   )
    | Declarations.Primitive(_) -> ("Primitive", hyps, None   )
    | Declarations.Symbol(_)    -> ("Symbol"   , hyps, None   )
  in
  let fields =
    ("name", `String(Names.Constant.to_string c)) ::
    ("kind", `String(kind)                      ) ::
    match def with
    | None      -> []
    | Some(def) ->
    let (ind_names, cst_names) = dep_names (term_deps hyps def) in
    let str s = `String(s) in
    ("inductive_deps", `List(List.map str ind_names)) ::
    ("constant_deps" , `List(List.map str cst_names)) :: []
  in
  let json : Yojson.Safe.t = `Assoc(fields) in
  let data = Yojson.Safe.pretty_to_string ~std:true json in
  Feedback.msg_notice (Pp.str data)

(* Ltac2 external: [term_deps : constr -> string list * string list] returns the
   immediate (inductive names, constant names) dependencies of a single term.
   This lets Ltac2 code compute the dependencies of an arbitrary term (e.g. a
   sub-term of a goal/spec), not just a defined constant. The result is returned
   as plain structured data, so callers can post-process it freely (e.g. build a
   JSON object, union over several terms, or look the names back up). *)
let () =
  let open Ltac2_plugin in
  let open Tac2ffi in
  let open Tac2externals in
  let define s =
    define Tac2expr.{ mltac_plugin = "rocq-term-deps"; mltac_tactic = s }
  in
  define "term_deps" (constr @-> ret (pair (list string) (list string))) (fun t ->
    dep_names (term_deps [] (EConstr.Unsafe.to_constr t)))

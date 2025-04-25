type t = Names.Cset.t * Names.Mindset.t

let term_deps : Constr.named_context -> Constr.t -> t = fun hyps t ->
  let constants = ref Names.Cset.empty in
  let inductives = ref Names.Mindset.empty in
  let rec term_deps t =
    let _ =
      match Constr.kind t with
      | Constr.Const((c,_))     ->
          constants := Names.Cset.add c !constants
      | Constr.Ind((i,_))       ->
          inductives := Names.Mindset.add (fst i) !inductives
      | Constr.Construct((c,_)) ->
          inductives := Names.Mindset.add (fst (fst c)) !inductives
      | _                       ->
          ()
    in
    Constr.iter term_deps t
  in
  List.iter (Context.Named.Declaration.iter_constr term_deps) hyps;
  term_deps t;
  (!constants, !inductives)

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
  let inductives = Names.Mindset.elements inductives in
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
    let (constants, inductives) = term_deps hyps def in
    let constants = Names.Cset.elements constants in
    let inductives = Names.Mindset.elements inductives in
    let make_ind i = `String(Names.MutInd.to_string i) in
    let make_cst c = `String(Names.Constant.to_string c) in
    ("inductive_deps", `List(List.map make_ind inductives)) ::
    ("constant_deps" , `List(List.map make_cst constants) ) :: []
  in
  let json : Yojson.Safe.t = `Assoc(fields) in
  let data = Yojson.Safe.pretty_to_string ~std:true json in
  Feedback.msg_notice (Pp.str data)

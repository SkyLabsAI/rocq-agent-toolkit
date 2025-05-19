open Ltac2_derive_plugin
open Ltac2_plugin
open Tac2expr

let derive : Derive.deriver = fun ts ->
  let expr_var s =
    let q = Libnames.qualid_of_ident (Names.Id.of_string s) in
    CAst.make Tac2expr.(CTacRef(RelId(q)))
  in
  let expr_var_x i = expr_var (Printf.sprintf "x%i" i) in
  let pat_var s =
    CAst.make (Tac2expr.CPatVar(Names.Name.Name(Names.Id.of_string s)))
  in
  let pat_var_x i = pat_var (Printf.sprintf "x%i" i) in
  let rec build ty arg =
    match ty with
    | GTypVar(i)             ->
        let json_of_ai = Printf.sprintf "json_of_a%i" i in
        CAst.make (CTacApp(expr_var json_of_ai, [arg]))
    | GTypArrow(_,_)         ->
        CErrors.user_err Pp.(str "function types not supported")
    | GTypRef(Tuple(n), tys) ->
        let p =
          let ps = List.init n pat_var_x in
          CAst.make (CPatRef(AbsKn(Tuple(n)), ps))
        in
        let v =
          let vs = List.mapi (fun i ty -> build ty (expr_var_x i)) tys in
          Tac2quote.of_list Fun.id vs
        in
        let tuple = "skylabs_ai.ltac2_json.JSON.Tuple" in
        let tuple = Libnames.qualid_of_string tuple in
        let tuple = CAst.make (CTacCst(RelId(tuple))) in
        let v = CAst.make (CTacApp(tuple, [v])) in
        CAst.make (CTacCse(arg, [(p, v)]))
    | GTypRef(Other(c), tys) ->
        let args =
          let make ty =
            let body = build ty (expr_var "x") in
            CAst.make (CTacFun([pat_var "x"], body))
          in
          List.fold_right (fun ty args -> make ty :: args) tys [arg]
        in
        let f =
          let c = Tac2env.shortest_qualid_of_type c in
          let c = Names.Id.to_string (Libnames.qualid_basename c) in
          expr_var ("json_of_" ^ c)
        in
        CAst.make (CTacApp(f, args))
  in
  let derive_one : type_constant -> Names.lname * raw_tacexpr = fun t ->
    let q = Tac2env.shortest_qualid_of_type t in
    let (nb_params, tydef) = Tac2env.interp_type t in
    let v =
      match tydef with
      | GTydDef(None)                      ->
          CErrors.user_err Pp.(str "abstract types not supported")
      | GTydDef(Some(ty))                  ->
          build ty (expr_var "x")
      | GTydAlg({galg_constructors=cs; _}) ->
          let make_case (_, c, tys) =
            let p =
              let c = Libnames.qualid_of_ident c in
              let c = Tac2env.locate_constructor c in
              let ps = List.mapi (fun i _ -> pat_var_x i) tys in
              CAst.make (CPatRef(AbsKn(Other(c)), ps))
            in
            let args = List.mapi (fun i ty -> build ty (expr_var_x i)) tys in
            let args =
              match args with
              | [] ->
                  let none = Libnames.qualid_of_string "Ltac2.Init.None" in
                  CAst.make (CTacCst(RelId(none)))
              | _  ->
                  let args = Tac2quote.of_list Fun.id args in
                  let tuple = "skylabs_ai.ltac2_json.JSON.Tuple" in
                  let tuple = Libnames.qualid_of_string tuple in
                  let tuple = CAst.make (CTacCst(RelId(tuple))) in
                  let args = CAst.make (CTacApp(tuple, [args])) in
                  let some = Libnames.qualid_of_string "Ltac2.Init.Some" in
                  let some = CAst.make (CTacCst(RelId(some))) in
                  CAst.make (CTacApp(some, [args]))
            in
            let c = CAst.make (CTacAtm(AtmStr(Names.Id.to_string c))) in
            let variant = "skylabs_ai.ltac2_json.JSON.Variant" in
            let variant = Libnames.qualid_of_string variant in
            let variant = CAst.make (CTacCst(RelId(variant))) in
            (p, CAst.make (CTacApp(variant, [c; args])))
          in
          CAst.make (CTacCse(expr_var "x", List.map make_case cs))
      | GTydRec(fs)                        ->
          let x = expr_var "x" in
          let make_field (f, _, ty) =
            let proj = Libnames.qualid_of_ident f in
            let fv = CAst.make (CTacPrj(x, RelId(proj))) in
            let name = CAst.make (CTacAtm(AtmStr(Names.Id.to_string f))) in
            let pair = CAst.make (CTacCst(AbsKn(Tuple(2)))) in
            CAst.make (CTacApp(pair, [name; build ty fv]))
          in
          let fs = Tac2quote.of_list Fun.id (List.map make_field fs) in
          let assoc = "skylabs_ai.ltac2_json.JSON.Assoc" in
          let assoc = Libnames.qualid_of_string assoc in
          let assoc = CAst.make (CTacCst(RelId(assoc))) in
          CAst.make (CTacApp(assoc, [fs]))
      | GTydOpn                            ->
          CErrors.user_err Pp.(str "open variant types not supported")
    in
    let ty =
      let ty_vars =
        List.init nb_params @@ fun i ->
        let s = Printf.sprintf "a%i" i in
        CAst.make (CTypVar(Names.Name.Name(Names.Id.of_string s)))
      in
      let json =
        let json = "skylabs_ai.ltac2_json.JSON.t" in
        CAst.make (CTypRef(RelId(Libnames.qualid_of_string json), []))
      in
      let ret_ty =
        CAst.make (CTypArrow(CAst.make (CTypRef(RelId(q), ty_vars)), json))
      in
      let add_arg var ty =
        CAst.make (CTypArrow(CAst.make (CTypArrow(var, json)), ty))
      in
      List.fold_right add_arg ty_vars ret_ty
    in
    let ps =
      List.init nb_params @@ fun i ->
      pat_var (Printf.sprintf "json_of_a%i" i)
    in
    let ps = ps @ [pat_var "x"] in
    let lid =
      let base = Names.Id.to_string (Libnames.qualid_basename q) in
      CAst.make (Names.Name.Name(Names.Id.of_string ("json_of_" ^ base)))
    in
    (lid, CAst.make (CTacCnv(CAst.make (CTacFun(ps, v)), ty)))
  in
  [StrVal(false, true, List.map derive_one ts)]

let _ =
  Derive.register_deriver "json" derive

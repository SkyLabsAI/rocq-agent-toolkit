open Ltac2_plugin
open Tac2expr

type deriver = type_constant list -> strexpr list

let derivers : deriver Names.Id.Map.t ref =
  Summary.ref ~name:"derivers" Names.Id.Map.empty

let register_deriver : string -> deriver -> unit = fun id d ->
  let id = Names.Id.of_string id in
  if Names.Id.Map.mem id !derivers then
    CErrors.user_err Pp.(str "a deriver is already defined with key" ++
      spc () ++ Names.Id.print id ++ str ".");
  derivers := Names.Id.Map.add id d !derivers

let list_derivers : unit -> unit = fun _ ->
  let ds = Names.Id.Map.fold (fun id _ acc -> id :: acc) !derivers [] in
  let pp =
    if ds = [] then Pp.str "No available derivers." else
    Pp.(str "Available derivers: " ++ pr_enum Names.Id.print ds ++ str ".")
  in
  Feedback.msg_notice pp

let run_deriver : Attributes.vernac_flags -> Names.Id.t -> deriver ->
    type_constant list -> unit = fun attrs id d ts ->
  try List.iter (Tac2entries.register_struct attrs) (d ts) with
  | CErrors.UserError(pp) as e ->
      let info = Exninfo.info e in
      CErrors.user_err ~info Pp.(str "failed while running deriver" ++
        spc () ++ Names.Id.print id ++ spc () ++ str "with" ++ spc () ++ pp)

let derive : Attributes.vernac_flags -> Names.Id.t list ->
    Libnames.qualid list -> unit = fun attrs ds ts ->
  (* Collect the derivers. *)
  let ds : (Names.Id.t * deriver) list =
    let processed = ref Names.Id.Set.empty in
    let error id s =
      CErrors.user_err Pp.(str "deriver" ++ spc () ++
        Names.Id.print id ++ spc () ++ str s ++ str ".")
    in
    let get_deriver id =
      if Names.Id.Set.mem id !processed then error id "already specified";
      processed := Names.Id.Set.add id !processed;
      match Names.Id.Map.find_opt id !derivers with
      | Some(d) -> (id, d)
      | None    -> error id "does not exist"
    in
    List.map get_deriver ds
  in
  (* Collect the types. *)
  let ts : type_constant list =
    let processed = ref Names.KNset.empty in
    let get_type q =
      let t =
        try Tac2env.locate_type q with Not_found ->
        CErrors.user_err Pp.(str "Qualified identifier" ++ spc () ++
          Libnames.pr_qualid q ++ spc () ++
          str "does not correspond to a Ltac2 type.")
      in
      if Names.KNset.mem t !processed then
        CErrors.user_err Pp.(str "Ltac2 type" ++ spc () ++
          Names.KerName.print t ++ spc () ++ str "already specified.");
      processed := Names.KNset.add t !processed;
      t
    in
    List.map get_type ts
  in
  (* Run the derivers. *)
  List.iter (fun (id, d) -> run_deriver attrs id d ts) ds

(** [is_prefix pfx mp] indicates whether the identifier list [pfx] is a prefix
    of the module path [mp]. Note that [false] is returned in the case where a
    bound module is used in [mp]. *)
let is_prefix : Names.Id.t list -> Names.ModPath.t -> bool = fun pfx mp ->
  let rec decompose ids mp =
    match mp with
    | Names.MPbound(_)  -> None
    | Names.MPdot(mp,l) -> decompose (Names.Label.to_id l :: ids) mp
    | Names.MPfile(dp)  ->
        let dp = Names.DirPath.repr dp in
        Some(List.rev_append dp (List.rev ids))
  in
  match decompose [] mp with None -> false | Some(ids) ->
  let rec is_prefix pfx ids =
    match (pfx, ids) with
    | ([]      , _        ) -> true
    | (_       , []       ) -> false
    | (p :: pfx, id :: ids) -> Names.Id.equal p id && is_prefix pfx ids
  in
  is_prefix pfx ids

module Constant = struct
  type t = {
    kername : string; (** Kernel name. *)
    about : string; (** About information. *)
  }
  [@@deriving yojson]

  type body = Declarations.constant_body
end

module Inductive = struct
  (* TODO add block info, including constructor and projections *)
  type t = {
    kername : string; (** Kernel name (for the mutual block). *)
    print : string; (** Printed mutual block (includes args info). *)
    about : string list; (* About info for each type in the mutual block. *)
  }
  [@@deriving yojson]

  type body = Declarations.mutual_inductive_body
end

module Data = struct
  type t = {
    constants : Constant.t list;
    inductives : Inductive.t list;
  }
  [@@deriving yojson]
end

type ('a, 'b, 'c) maker =
  Environ.env -> Evd.evar_map -> Names.KerName.t -> 'a -> 'b -> 'c

let build_constant : (Names.Constant.t, Constant.body, Constant.t) maker =
    fun env sigma kn c _ ->
  let about =
    let q =
      let gr = Names.GlobRef.ConstRef(c) in
      let q = Nametab.shortest_qualid_of_global Names.Id.Set.empty gr in
      CAst.make (Constrexpr.AN q)
    in
    let about = Prettyp.print_about env sigma q None in
    Pp.(string_of_ppcmds (hov 2 about))
  in
  Constant.{kername = Names.KerName.to_string kn; about}

let build_inductive : (Names.MutInd.t, Inductive.body, Inductive.t) maker =
    fun env sigma kn m body ->
  let kername = Names.KerName.to_string kn in
  let print =
    let q =
      let gr = Names.GlobRef.IndRef(m, 0) in
      let q = Nametab.shortest_qualid_of_global Names.Id.Set.empty gr in
      CAst.make (Constrexpr.AN q)
    in
    let access = Global.{access_proof = fun _ -> None} in 
    let print = Prettyp.print_name access env sigma q None in
    Pp.(string_of_ppcmds (hov 2 print))
  in
  let about =
    List.init body.Declarations.mind_ntypes @@ fun i ->
    let q =
      let gr = Names.GlobRef.IndRef(m, i) in
      let q = Nametab.shortest_qualid_of_global Names.Id.Set.empty gr in
      CAst.make (Constrexpr.AN q)
    in
    let about = Prettyp.print_about env sigma q None in
    Pp.(string_of_ppcmds (hov 2 about))
  in
  Inductive.{kername; print; about}

let build_data : Names.DirPath.t list -> Data.t = fun ds ->
  let ds = List.map (fun d -> List.rev (Names.DirPath.repr d)) ds in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let constants =
    Environ.fold_constants (fun c body acc ->
      let kn = Names.Constant.user c in
      let mp = Names.KerName.modpath kn in
      match List.exists (fun d -> is_prefix d mp) ds || ds = [] with
      | false -> acc
      | true  -> build_constant env sigma kn c body :: acc
    ) env []
  in
  let inductives =
    Environ.fold_inductives (fun m body acc ->
      let kn = Names.MutInd.user m in
      let mp = Names.KerName.modpath kn in
      match List.exists (fun d -> is_prefix d mp) ds || ds = [] with
      | false -> acc
      | true  -> build_inductive env sigma kn m body :: acc
    ) env []
  in
  Data.{constants; inductives}

let print_env : Names.DirPath.t list -> unit = fun ds ->
  let data = Data.to_yojson (build_data ds) in
  let data = Yojson.Safe.pretty_to_string ~std:true data in
  Feedback.msg_notice (Pp.str data)

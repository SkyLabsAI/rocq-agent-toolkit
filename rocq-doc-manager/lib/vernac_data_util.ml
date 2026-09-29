let command_attrs v =
  match snd v.CAst.v with
  | Vernacexpr.VernacSynterp(e) ->
      begin
        let open Rocq_vernac_entry in
        match e with
        | EVernacBeginSection(id)
        | EVernacEndSegment(id)
        | EVernacDeclareModule(id) ->
            [("id", `String(Names.Id.to_string id.CAst.v))]
        | EVernacDeclareModuleType{id; has_body}
        | EVernacDefineModule{id; has_body} ->
            [("id", `String(Names.Id.to_string id.CAst.v));
              ("defn", `Bool(has_body))]
        | _ -> []
      end
  | Vernacexpr.VernacSynPure(e) ->
      begin
        let open Vernacexpr in
        match e with
        | VernacDefinition((_,kind), (id, _),e) ->
            let id = Pp.string_of_ppcmds (Names.Name.print id.CAst.v) in
            let proof =
              match e with
              | ProveBody(_,_)      -> true
              | DefineBody(_,_,_,_) -> false
            in
            let kind =
              let open Decls in
              match kind with
              | Definition -> "Definition"
              | Coercion -> "Coercion"
              | SubClass -> "SubClass"
              | CanonicalStructure -> "CanonicalStructure"
              | Example -> "Example"
              | Fixpoint -> "Fixpoint"
              | CoFixpoint -> "CoFixpoint"
              | Scheme -> "Scheme"
              | StructureComponent -> "StructureComponent"
              | IdentityCoercion -> "IdentityCoercion"
              | Instance -> "Instance"
              | Method -> "Method"
              | Let -> "Let"
              | LetContext -> "LetContext"
            in
            let id = `String(id) in
            let proof = `Bool(proof) in
            let kind = `String(kind) in
            [("id", id); ("kind", kind); ("proof", proof)]
        | VernacStartTheoremProof(kind, proof_exprs) ->
            let ids =
              let to_id ((id, _), _) =
                `String(Names.Id.to_string id.CAst.v)
              in
              List.map to_id proof_exprs
            in
            let kind =
              let open Decls in
              match kind with
              | Theorem -> "Theorem"
              | Lemma -> "Lemma"
              | Fact -> "Fact"
              | Remark -> "Remark"
              | Property -> "Property"
              | Proposition -> "Proposition"
              | Corollary -> "Corollary"
            in
            [("ids", `List(ids)); ("kind", `String(kind))]
        | VernacEndProof(proof_end) ->
            let kind =
              match proof_end with
              | Admitted -> "Admitted"
              | Proved(Opaque, _) -> "Qed"
              | Proved(Transparent, _) -> "Defined"
            in
            [("kind", `String(kind))]
        | _ -> []
      end

type entry =
  | EVernacNoop
  | EVernacNotation
  | EVernacBeginSection of Names.lident
  | EVernacEndSegment of Names.lident
  | EVernacRequire
  | EVernacImport
  | EVernacDeclareModule of Names.lident
  | EVernacDefineModule of Names.lident
  | EVernacDeclareModuleType of Names.lident
  | EVernacInclude
  | EVernacSetOption
  | EVernacLoad
  | EVernacExtend

type command = entry Vernacexpr.vernac_expr_gen CAst.t

let of_vernac_control_gen_r : ('b -> entry) ->
    ('a, 'b) Vernacexpr.vernac_control_gen_r CAst.t -> command =
    fun of_entry CAst.{loc; v} ->
  let v =
    let open Vernacexpr in
    match v.expr with
    | VernacSynPure(e) -> VernacSynPure(e)
    | VernacSynterp(e) -> VernacSynterp(of_entry e)
  in
  CAst.make ?loc v

let of_vernac_control : Vernacexpr.vernac_control -> command =
  let translate_entry e =
    let open Vernacexpr in
    match e with
    | VernacLoad(_,_) -> EVernacLoad
    | VernacReservedNotation(_,_)
    | VernacNotation(_,_)
    | VernacDeclareCustomEntry(_) -> EVernacNotation
    | VernacBeginSection(lid) -> EVernacBeginSection(lid)
    | VernacEndSegment(lid) -> EVernacEndSegment(lid)
    | VernacRequire(_,_,_) -> EVernacRequire
    | VernacImport(_,_) -> EVernacImport
    | VernacDeclareModule(_,lid,_,_) -> EVernacDeclareModule(lid)
    | VernacDefineModule(_,lid,_,_,_) -> EVernacDefineModule(lid)
    | VernacDeclareModuleType(lid,_,_,_) -> EVernacDeclareModuleType(lid)
    | VernacInclude(_) -> EVernacInclude
    | VernacDeclareMLModule(_)
    | VernacChdir(_)
    | VernacExtraDependency(_) -> EVernacNoop
    | VernacSetOption(_,_,_) -> EVernacSetOption
    | VernacProofMode(_) -> EVernacSetOption
    | VernacExtend(_,_) -> EVernacExtend
  in
  of_vernac_control_gen_r translate_entry

let of_vernac_control_entry : Synterp.vernac_control_entry -> command =
  let translate_entry e =
    match e with
    | Synterp.EVernacNoop -> EVernacNoop
    | Synterp.EVernacNotation(_) -> EVernacNotation
    | Synterp.EVernacBeginSection(i) -> EVernacBeginSection(i)
    | Synterp.EVernacEndSegment(i) -> EVernacEndSegment(i)
    | Synterp.EVernacRequire(_) -> EVernacRequire
    | Synterp.EVernacImport(_) -> EVernacImport
    | Synterp.EVernacDeclareModule(_,i,_,_) -> EVernacDeclareModule(i)
    | Synterp.EVernacDefineModule(_,i,_,_,_,_) -> EVernacDefineModule(i)
    | Synterp.EVernacDeclareModuleType(i,_,_,_,_) -> EVernacDeclareModuleType(i)
    | Synterp.EVernacInclude(_) -> EVernacInclude
    | Synterp.EVernacSetOption(_) -> EVernacSetOption
    | Synterp.EVernacLoad(_) -> EVernacLoad
    | Synterp.EVernacExtend(_) -> EVernacExtend
  in
  of_vernac_control_gen_r translate_entry

let synterp_descr : entry -> string = fun e ->
  match e with
  | EVernacNoop                 -> "Noop"
  | EVernacNotation             -> "Notation"
  | EVernacBeginSection(_)      -> "BeginSection"
  | EVernacEndSegment(_)        -> "EndSegment"
  | EVernacRequire              -> "Require"
  | EVernacImport               -> "Import"
  | EVernacDeclareModule(_)     -> "DeclareModule"
  | EVernacDefineModule(_)      -> "DefineModule"
  | EVernacDeclareModuleType(_) -> "DeclareModuleType"
  | EVernacInclude              -> "Include"
  | EVernacSetOption            -> "SetOption"
  | EVernacLoad                 -> "Load"
  | EVernacExtend               -> "Extend"

let synpure_descr : Vernacexpr.synpure_vernac_expr -> string = fun e ->
  let open Vernacexpr in
  match e with
  (* Syntax *)
  | VernacOpenCloseScope(_,_)        -> "OpenCloseScope"
  | VernacDeclareScope(_)            -> "DeclareScope"
  | VernacDelimiters(_,_)            -> "Delimiters"
  | VernacBindScope(_,_)             -> "BindScope"
  | VernacEnableNotation(_,_,_,_,_)  -> "EnableNotation"

  (* Gallina *)
  | VernacDefinition(_,_,_)          -> "Definition"
  | VernacStartTheoremProof(_,_)     -> "StartTheoremProof"
  | VernacEndProof(_)                -> "EndProof"
  | VernacExactProof(_)              -> "ExactProof"
  | VernacAssumption(_,_,_)          -> "Assumption"
  | VernacSymbol(_)                  -> "Symbol"
  | VernacInductive(_,_)             -> "Inductive"
  | VernacFixpoint(_,_)              -> "Fixpoint"
  | VernacCoFixpoint(_,_)            -> "CoFixpoint"
  | VernacScheme(_)                  -> "Scheme"
  | VernacSchemeEquality(_,_)        -> "SchemeEquality"
  | VernacCombinedScheme(_,_)        -> "CombinedScheme"
  | VernacUniverse(_)                -> "Universe"
  | VernacSort(_)                    -> "Sort"
  | VernacConstraint(_)              -> "Constraint"
  | VernacAddRewRule(_,_)            -> "AddRewRule"

  (* Gallina extensions *)
  | VernacCanonical(_)               -> "Canonical"
  | VernacCoercion(_,_)              -> "Coercion"
  | VernacIdentityCoercion(_,_,_)    -> "IdentityCoercion"
  | VernacNameSectionHypSet(_,_)     -> "NameSectionHypSet"

  (* Type classes *)
  | VernacInstance(_,_,_,_,_)        -> "Instance"
  | VernacDeclareInstance(_,_,_,_)   -> "DeclareInstance"
  | VernacContext(_)                 -> "Context"
  | VernacExistingInstance(_)        -> "ExistingInstance"
  | VernacExistingClass(_)           -> "ExistingClass"

  (* Resetting *)
  | VernacResetName(_)               -> "ResetName"
  | VernacResetInitial               -> "ResetInitial"
  | VernacBack(_)                    -> "Back"

  (* Commands *)
  | VernacCreateHintDb(_,_)          -> "CreateHintDb"
  | VernacRemoveHints(_,_)           -> "RemoveHints"
  | VernacHints(_,_)                 -> "Hints"
  | VernacSyntacticDefinition(_,_,_) -> "SyntacticDefinition"
  | VernacArguments(_,_,_,_)         -> "Arguments"
  | VernacReserve(_)                 -> "Reserve"
  | VernacGeneralizable(_)           -> "Generalizable"
  | VernacSetOpacity(_,_)            -> "SetOpacity"
  | VernacSetStrategy(_)             -> "SetStrategy"
  | VernacMemOption(_,_)             -> "MemOption"
  | VernacPrintOption(_)             -> "PrintOption"
  | VernacCheckMayEval(_,_,_)        -> "CheckMayEval"
  | VernacGlobalCheck(_)             -> "GlobalCheck"
  | VernacDeclareReduction(_,_)      -> "DeclareReduction"
  | VernacPrint(_)                   -> "Print"
  | VernacSearch(_,_,_)              -> "Search"
  | VernacLocate(_)                  -> "Locate"
  | VernacRegister(_,_)              -> "Register"
  | VernacPrimitive(_,_,_)           -> "Primitive"
  | VernacComments(_)                -> "Comments"
  | VernacAttributes(_)              -> "Attributes"

  (* Proof management *)
  | VernacAbort                      -> "Abort"
  | VernacAbortAll                   -> "AbortAll"
  | VernacRestart                    -> "Restart"
  | VernacUndo(_)                    -> "Undo"
  | VernacUndoTo(_)                  -> "UndoTo"
  | VernacFocus(_)                   -> "Focus"
  | VernacUnfocus                    -> "Unfocus"
  | VernacUnfocused                  -> "Unfocused"
  | VernacBullet(_)                  -> "Bullet"
  | VernacSubproof(_)                -> "Subproof"
  | VernacEndSubproof                -> "EndSubproof"
  | VernacShow(_)                    -> "Show"
  | VernacCheckGuard                 -> "CheckGuard"
  | VernacValidateProof              -> "ValidateProof"
  | VernacProof(_,_)                 -> "Proof"

  | VernacAddOption(_,_)             -> "AddOption"
  | VernacRemoveOption(_,_)          -> "RemoveOption"

let command_tag c =
  let open Vernacexpr in
  match c.CAst.v with
  | VernacSynterp(e) -> "synterp:" ^ synterp_descr e
  | VernacSynPure(e) -> "synpure:" ^ synpure_descr e

let command_to_yojson c =
  `String(command_tag c)

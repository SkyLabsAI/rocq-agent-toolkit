open Rocq_split

let synterp_desc : Rocq_split.entry -> string = fun e ->
  match e with
  | EVernacNoop                 -> "Noop"
  | EVernacNotation             -> "Notation"
  | EVernacBeginSection(_)      -> "BeginSection"
  | EVernacEndSegment(_)        -> "EndSegment"
  | EVernacRequire              -> "Require"
  | EVernacImport               -> "Import"
  | EVernacDeclareModule(_,_)   -> "DeclareModule"
  | EVernacDefineModule(_,_)    -> "DefineModule"
  | EVernacDeclareModuleType(_) -> "DeclareModuleType"
  | EVernacInclude              -> "Include"
  | EVernacSetOption            -> "SetOption"
  | EVernacLoad                 -> "Load"
  | EVernacExtend               -> "Extend"

let synpure_desc : Vernacexpr.synpure_vernac_expr -> string = fun e ->
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

let descr_kind k =
  match k with
  | `Blanks     -> "blanks"
  | `Command(c) ->
  let open Vernacexpr in
  match c.CAst.v with
  | VernacSynterp(e) -> "synterp:" ^ synterp_desc e
  | VernacSynPure(e) -> "synpure:" ^ synpure_desc e

let sentence_to_json {kind; text; bp; ep} =
  `Assoc([
    ("kind", `String(descr_kind kind));
    ("text", `String(text)           );
    ("bp"  , `Int(bp)                );
    ("ep"  , `Int(ep)                );
  ])

let output_error error {parsed_sentences = sentences; error_loc = loc} =
  let loc = match loc with Some(loc) -> Rocq_loc.to_yojson loc | _ -> `Null in
  let sentences = List.map sentence_to_json sentences in
  let json =
    `Assoc([
      ("error", `String(error)  );
      ("loc"  , loc             );
      ("Items", `List(sentences));
    ])
  in
  Format.printf "%a\n%!" (Yojson.Safe.pretty_print ~std:true) json

let output_result file {dirpath; sentences} =
  let dirpath = Names.DirPath.to_string dirpath in
  let sentences = List.map sentence_to_json sentences in
  let json =
    `Assoc([
      ("file"   , `String(file)   );
      ("dirpath", `String(dirpath));
      ("items"  , `List(sentences));
    ])
  in
  Format.printf "%a\n%!" (Yojson.Safe.pretty_print ~std:true) json

let _ =
  let usage i =
    let prog = Sys.argv.(0) in
    Printf.eprintf "Usage: %s [-h|-help|--help] FILE [-- ROCQARGS]\n%!" prog;
    exit i
  in
  let (file, args) =
    let (argv, args) =
      match Array.find_index (String.equal "--") Sys.argv with
      | None    -> (Sys.argv, [])
      | Some(i) ->
      let argv = Array.sub Sys.argv 0 i in
      let args = Array.sub Sys.argv (i+1) (Array.length Sys.argv - i - 1) in
      (argv, Array.to_list args)
    in
    let argv = List.tl (Array.to_list argv) in
    let is_help arg = List.mem arg ["-h"; "-help"; "--help"] in
    match List.exists is_help argv with
    | true  -> usage 0
    | false ->
    match argv with
    | [file] -> (file, args)
    | _      -> usage 1
  in
  match Rocq_split.split_file ~file ~args with
  | Ok(data)       -> output_result file data
  | Error(s, data) -> output_error s data; exit 1

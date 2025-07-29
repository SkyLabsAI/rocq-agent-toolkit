type sentence = {
  kind : string;
  text : string;
  bp : int;
  ep : int;
}
[@@deriving yojson]

type feedback = Feedback.feedback list

type loc = Loc.t option

let feedbacks : feedback ref = ref []

type state = {
  root_state : Vernacstate.t;
  file : string;
  dirpath : Names.DirPath.t;
}

let get_file : state -> string = fun state ->
  state.file

let get_dirpath : state -> Names.DirPath.t = fun state ->
  state.dirpath

let dirpath_of_file file =
  let log_dir =
    try Loadpath.logical (Loadpath.find_load_path (Filename.dirname file))
    with Not_found -> Libnames.default_root_prefix
  in
  let base = Filename.remove_extension (Filename.basename file) in
  Libnames.add_dirpath_suffix log_dir (Names.Id.of_string base)

let init : argv:string array -> (state, string) result = fun ~argv ->
  Flags.quiet := true;
  System.trust_file_cache := true;
  Coqinit.init_ocaml ();
  let usage =
    let executable_name = "rocq_split" in
    Boot.Usage.{executable_name; extra_args = ""; extra_options = ""}
  in
  try
    let parse_extra _ files = (files, []) in
    let (args, files) =
      let args = List.tl (Array.to_list argv) in
      Coqinit.parse_arguments ~parse_extra args
    in
    ignore (Feedback.add_feeder (fun fb -> feedbacks := fb :: !feedbacks));
    Coqinit.init_runtime ~usage args;
    Coqinit.init_document args;
    match files with
    | []          -> Error("Missing file argument.")
    | _ :: _ :: _ -> Error("More than one file argument.")
    | [file]      ->
    let dirpath = dirpath_of_file file in
    let injs = Coqargs.injection_commands args in
    Coqinit.start_library ~intern:Vernacinterp.fs_intern ~top:dirpath injs;
    let root_state = Vernacstate.freeze_full_state () in
    Ok({root_state; file; dirpath})
  with e ->
    Format.(fprintf str_formatter "@[%a@]%!" Pp.pp_with (CErrors.print e));
    Error(Format.flush_str_formatter ())

let synterp_desc : Synterp.synterp_entry -> string = fun e ->
  let open Synterp in
  match e with
  | EVernacNoop                         -> "Noop"
  | EVernacNotation(_)                  -> "Notation"
  | EVernacBeginSection(_)              -> "BeginSection"
  | EVernacEndSegment(_)                -> "EndSegment"
  | EVernacRequire(_,_,_,_)             -> "Require"
  | EVernacImport(_,_)                  -> "Import"
  | EVernacDeclareModule(_,_,_,_)       -> "DeclareModule"
  | EVernacDefineModule(_,_,_,_,_,_)    -> "DefineModule"
  | EVernacDeclareModuleType(_,_,_,_,_) -> "DeclareModuleType"
  | EVernacInclude(_)                   -> "Include"
  | EVernacSetOption(_)                 -> "SetOption"
  | EVernacLoad(_,_)                    -> "Load"
  | EVernacExtend(_)                    -> "Extend"

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

let commands_data file cmds =
  In_channel.with_open_text file @@ fun ic ->
  let cur_offset = ref 0 in
  let buf = Buffer.create 73 in
  let rev_items = ref [] in
  let add_blanks text bp ep =
    let item = {kind = "blanks"; text; bp; ep} in
    rev_items := item :: !rev_items
  in
  let add_command cmd Loc.{bp; ep; _} text =
    let kind =
      let open Vernacexpr in
      match cmd.CAst.v.expr with
      | VernacSynterp(e) -> "synterp:" ^ synterp_desc e
      | VernacSynPure(e) -> "synpure:" ^ synpure_desc e
    in
    let item = {kind; text; bp; ep} in
    rev_items := item :: !rev_items
  in
  let handle_cmd cmd =
    let loc = Option.get cmd.CAst.loc in
    (* Parse blanks up to the beginning position. *)
    Buffer.clear buf;
    let bp = !cur_offset in
    while !cur_offset < loc.Loc.bp do
      incr cur_offset;
      match In_channel.input_char ic with
      | None   -> invalid_arg "position error xxx"
      | Some c -> Buffer.add_char buf c
    done;
    let blanks = Buffer.contents buf in
    if blanks <> "" then add_blanks blanks bp !cur_offset;
    (* Parse the actual command. *)
    Buffer.clear buf;
    while !cur_offset < loc.Loc.ep do
      incr cur_offset;
      match In_channel.input_char ic with
      | None   -> invalid_arg "position error yyy"
      | Some c -> Buffer.add_char buf c
    done;
    add_command cmd loc (Buffer.contents buf)
  in
  List.iter handle_cmd cmds;
  List.rev !rev_items

let parse stream =
  let mode = Some (Synterp.get_default_proof_mode ()) in
  let cmd = Procq.Entry.parse (Pvernac.main_entry mode) stream in
  Option.map (Synterp.synterp_control ~intern:Vernacinterp.fs_intern) cmd

let get : state -> (sentence list, loc * string) result * feedback =
    fun state ->
  feedbacks := [];
  try
    Vernacstate.unfreeze_full_state state.root_state;
    In_channel.with_open_text state.file @@ fun ic ->
    let loc = Loc.(initial (InFile {dirpath = None; file = state.file})) in
    let stream = Procq.Parsable.make ~loc (Gramlib.Stream.of_channel ic) in
    let rec loop rev_cmds =
      match parse stream with
      | None      -> List.rev rev_cmds
      | Some(cmd) -> loop (cmd :: rev_cmds)
    in
    let cmds = loop [] in
    let data = commands_data state.file cmds in
    (Ok data, List.rev !feedbacks)
  with e ->
    let (e, info) = Exninfo.capture e in
    let loc = Loc.get_loc info in
    let err =
      Format.(fprintf str_formatter "@[%a@]%!" Pp.pp_with (CErrors.print e));
      Format.flush_str_formatter ()
    in
    (Error (loc, err), List.rev !feedbacks)

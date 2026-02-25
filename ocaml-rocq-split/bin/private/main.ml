let dirpath_of_file file =
  let log_dir =
    try Loadpath.logical (Loadpath.find_load_path (Filename.dirname file))
    with Not_found -> Libnames.default_root_prefix
  in
  let base = Filename.remove_extension (Filename.basename file) in
  Libnames.add_dirpath_suffix log_dir (Names.Id.of_string base)

type command = Rocq_split_data.command

let parse stream =
  let mode = Some (Synterp.get_default_proof_mode ()) in
  let cmd = Procq.Entry.parse (Pvernac.main_entry mode) stream in
  Option.map (Synterp.synterp_control ~intern:Vernacinterp.fs_intern) cmd

let translate_entry e =
  let open Rocq_split_data in
  match e with
  | Synterp.EVernacNoop -> EVernacNoop
  | Synterp.EVernacNotation(_) -> EVernacNotation
  | Synterp.EVernacBeginSection(i) -> EVernacBeginSection(i)
  | Synterp.EVernacEndSegment(i) -> EVernacEndSegment(i)
  | Synterp.EVernacRequire(_) -> EVernacRequire
  | Synterp.EVernacImport(_) -> EVernacImport
  | Synterp.EVernacDeclareModule(e,i,_,_) -> EVernacDeclareModule(e,i)
  | Synterp.EVernacDefineModule(e,i,_,_,_,_) -> EVernacDefineModule(e,i)
  | Synterp.EVernacDeclareModuleType(i,_,_,_,_) -> EVernacDeclareModuleType(i)
  | Synterp.EVernacInclude(_) -> EVernacInclude
  | Synterp.EVernacSetOption(_) -> EVernacSetOption
  | Synterp.EVernacLoad(_) -> EVernacLoad
  | Synterp.EVernacExtend(_) -> EVernacExtend

let sentence_split : config:Rocq_split_data.config ->
    add_command:(command -> unit) ->
    (Names.DirPath.t, string * Rocq_loc.t option) result =
  fun ~config:{file; args; contents} ~add_command ->
  Flags.quiet := true;
  System.trust_file_cache := true;
  Coqinit.init_ocaml ();
  let usage =
    let executable_name = "rocq_split" in
    Boot.Usage.{executable_name; extra_args = ""; extra_options = ""}
  in
  let parse_extra _ files = (files, []) in
  let (args, files) = Coqinit.parse_arguments ~parse_extra args in
  Coqinit.init_runtime ~usage args;
  Coqinit.init_document args;
  match files with
  | _ :: _ -> Error("File passed as part of the arguments.", None)
  | []     ->
  let dirpath = dirpath_of_file file in
  let injs = Coqargs.injection_commands args in
  Coqinit.start_library ~intern:Vernacinterp.fs_intern ~top:dirpath injs;
  let loc = Loc.(initial (InFile {dirpath = None; file = file})) in
  let with_stream f =
    match contents with
    | Some(s) -> f (Gramlib.Stream.of_string s)
    | None    ->
        In_channel.with_open_text file @@ fun ic ->
        f (Gramlib.Stream.of_channel ic)
  in
  with_stream @@ fun stream ->
  let stream = Procq.Parsable.make ~loc stream in
  let rec loop () =
    match parse stream with
    | None                -> ()
    | Some(CAst.{loc; v}) ->
    let v =
      let open Vernacexpr in
      match v.expr with
      | VernacSynPure(e) -> VernacSynPure(e)
      | VernacSynterp(e) -> VernacSynterp(translate_entry e)
    in
    add_command (CAst.make ?loc v); loop ()
  in
  loop ();
  Ok(dirpath)

let make_collector : unit -> ('a -> unit) * (unit -> 'a list) = fun () ->
  let rev_data = ref [] in
  ((fun d -> rev_data := d :: !rev_data), (fun () -> List.rev !rev_data))

let sentence_split : Rocq_split_data.(config -> res) = fun config ->
  let (add_feedback, collect_feedback) = make_collector () in
  let (add_command , collect_commands) = make_collector () in
  let _ = Feedback.add_feeder add_feedback in
  let make_res result =
    let commands = collect_commands () in
    let feedback = collect_feedback () in
    Rocq_split_data.{commands; feedback; result}
  in
  try make_res (sentence_split ~config ~add_command) with e ->
  let (e, info) = Exninfo.capture e in
  let loc = Loc.get_loc info in
  let err =
    Format.(fprintf str_formatter "@[%a@]%!" Pp.pp_with (CErrors.print e));
    Format.flush_str_formatter ()
  in
  make_res (Error(err, loc))

let run : Rocq_split_data.(config -> res) -> unit = fun f ->
  Marshal.to_channel stdout (f (Marshal.from_channel stdin)) [];
  Out_channel.flush stdout

let _ =
  run sentence_split

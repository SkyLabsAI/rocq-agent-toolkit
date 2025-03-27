let command_category cmd =
  let open Vernacexpr in
  match cmd.CAst.v.expr with
  | VernacSynterp(_) -> "synterp"
  | VernacSynPure(_) -> "synpure"

let commands_data file dirpath cmds =
  In_channel.with_open_text file @@ fun ic ->
  let cur_offset = ref 0 in
  let buf = Buffer.create 73 in
  let rev_items = ref [] in
  let add_blanks text bp ep =
    let json =
      `Assoc [
        ("blanks", `String text);
        ("bp"    , `Int bp);
        ("ep"    , `Int ep);
      ]
    in
    rev_items := json :: !rev_items
  in
  let add_command cmd loc text =
    let json =
      let cat = command_category cmd in
      `Assoc [
        ("cmd", `String text);
        ("cat", `String cat);
        ("bp" , `Int loc.Loc.bp);
        ("ep" , `Int loc.Loc.ep);
       ]
    in
    rev_items := json :: !rev_items
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
  let dirpath = Names.DirPath.to_string dirpath in
  let items = List.rev !rev_items in
  `Assoc [
    ("file", `String file);
    ("dirpath", `String dirpath);
    ("items", `List items)
  ]

let intern = Vernacinterp.fs_intern

let parse stream =
  let mode = Some (Synterp.get_default_proof_mode ()) in
  let cmd = Procq.Entry.parse (Pvernac.main_entry mode) stream in
  Option.map (Synterp.synterp_control ~intern) cmd

let dirpath_of_file file =
  let log_dir =
    try Loadpath.logical (Loadpath.find_load_path (Filename.dirname file))
    with Not_found -> Libnames.default_root_prefix
  in
  let base = Filename.remove_extension (Filename.basename file) in
  Libnames.add_dirpath_suffix log_dir (Names.Id.of_string base)

let handle_file ~injections ~root_state file =
  Vernacstate.unfreeze_full_state root_state;
  In_channel.with_open_text file @@ fun ic ->
  let dirpath = dirpath_of_file file in
  Coqinit.start_library ~intern ~top:dirpath injections;
  let loc = Loc.(initial (InFile {dirpath = None; file})) in
  let stream = Procq.Parsable.make ~loc (Gramlib.Stream.of_channel ic) in
  let rec loop rev_cmds =
    match parse stream with
    | None      -> List.rev rev_cmds
    | Some(cmd) -> loop (cmd :: rev_cmds)
  in
  let cmds = loop [] in
  let pp_json ff json = Yojson.Basic.pretty_print ff json in
  Format.printf "%a\n%!" pp_json (commands_data file dirpath cmds)

let feeder fb =
  let open Feedback in
  match fb.contents with
  | Message ((Notice | Warning | Error), _, _, msg) ->
      Format.eprintf "%s@\n%!" Pp.(string_of_ppcmds msg)
  | _                                               -> ()

let _ =
  Flags.quiet := true;
  System.trust_file_cache := true;
  Coqinit.init_ocaml ();
  let usage =
    let open Boot.Usage in
    {executable_name = "rocq_split"; extra_args = ""; extra_options = ""}
  in
  try
    let parse_extra _ files = (files, []) in
    let (args, files) =
      let args = List.tl (Array.to_list Sys.argv) in
      Coqinit.parse_arguments ~parse_extra args
    in
    ignore (Feedback.add_feeder feeder);
    Coqinit.init_runtime ~usage args;
    Coqinit.init_document args;
    let injections = Coqargs.injection_commands args in
    let root_state = Vernacstate.freeze_full_state () in
    List.iter (handle_file ~injections ~root_state) files
  with e ->
    let (e, info) = Exninfo.capture e in
    let loc = Loc.get_loc info in
    let pr_loc loc = Pp.(Loc.pr loc ++ str ":" ++ fnl ()) in
    Format.eprintf "%a" Pp.pp_with (Pp.pr_opt pr_loc loc);
    Format.eprintf "Error: @[%a@]@\n%!" Pp.pp_with (CErrors.print e);
    exit 1

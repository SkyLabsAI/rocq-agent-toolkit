open Cmdliner
open Panic

let version = "dev"

let non_dir_file_with_ext : string -> string Arg.conv = fun ext ->
  let parse s =
    let err s = Error(`Msg(s)) in
    match Arg.(conv_parser non_dir_file s) with
    | Ok(s) when s = "-"                     ->
        err "\"-\" is not a valid Rocq source file name"
    | Ok(s) when Filename.extension s <> ext ->
        err (Printf.sprintf "\"%s\" does not have extension \"%s\"" s ext)
    | res -> res
  in
  Arg.conv (parse, Arg.conv_printer Arg.non_dir_file)

let rocq_file =
  let doc =
    "Path to an existing Rocq source file. The source file is expected to be \
     managed by a dune project, so that appropriate CLI arguments can be \
     automatically obtained."
  in
  let v_file = non_dir_file_with_ext ".v" in
  Arg.(required & pos 0 (some v_file) None & info [] ~docv:"FILE" ~doc)

let no_build_deps =
  let doc =
    "Disables the building of dependencies before starting the editor. This \
     option can be used to speed up the start-up in big projects, when the \
     user knows that dependencies are up-to-date. \
     WARNING: Only use this option if you know exactly what you are doing. \
     It will lead to failures, and, worse, false successes."
  in
  Arg.(value & flag & info ["no-build-deps"] ~doc)

let jobs =
  let doc =
    "Indicates that no more than $(docv) concurrent jobs should be run by \
     $(b,dune) when building dependencies. If $(b,--no-build-deps) is given, \
     this option is a no-op."
  in
  Arg.(value & opt (some int) None & info ["j"; "jobs"] ~doc ~docv:"JOBS")

let display =
  let display =
    let enum = ["progress"; "quiet"; "short"; "verbose"] in
    Arg.enum (List.map (fun m -> (m, m)) enum)
  in
  let doc =
    "Controls the display mode of $(b,dune) when building the dependencies \
     of the file to be processed. If $(b,--no-build-deps) is given, this \
     option is a no-op. Available values are: $(b,progress) (updated status \
     line), $(b,quiet) (only warnings and errors are displayed), $(b,short) \
     (adds one line per command), and $(b,verbose) (full command line is \
     printed)."
  in
  let i = Arg.info ["display"] ~docv:"MODE" ~doc in
  Arg.(value & opt display "progress" & i)

let dune_config =
  let build no_build jobs display = Dune_util.{no_build; jobs; display} in
  Term.(const build $ no_build_deps $ jobs $ display)

let daemonize =
    let doc =
      "Indicates whether the `rocq-ed init` runs as a daemon"
    in
    Arg.(value & opt bool true & info ["d"; "daemonize"] ~doc ~docv:"DAEMONIZE")

let init_cmd =
  let doc =
    "Starts a CLI editor session for the given Rocq source file. Note that \
     when a session for a given source file is running, no other session can \
     be started on the same file."
  in
  let term = Term.(const Protocol.init $ daemonize $ dune_config $ rocq_file) in
  Cmd.(make (info "init" ~version ~doc) term)

let stop_cmd =
  let doc =
    "Stop the running CLI editor session for the given Rocq source file."
  in
  let term = Term.(const Protocol.stop $ rocq_file) in
  Cmd.(make (info "stop" ~version ~doc) term)

let context_lines =
  let doc =
    "Print $(docv) lines of context before and after the cursor instead of \
     printing the whole Rocq document."
  in
  Arg.(value & opt (some int) (Some 5) &
    info ["C"; "context-lines"] ~doc ~docv:"NUM")

let auto_print rocq_file =
  let Ok(status) = Protocol.client_request rocq_file Request.(Status({context=Some(5)})) in
  let Ok(goals) = Protocol.client_request rocq_file Request.Goals in
  Printf.printf("%s\n%s%!") status goals

let with_auto_print : (string -> unit) -> (string -> unit) = fun f rocq_file ->
  f rocq_file;
  auto_print rocq_file

let status_cmd =
  let doc =
    "Print the current contents of the Rocq document, including the position \
     of the cursor marked as $(b,<CURSOR>)."
  in
  let run context rocq_file =
    match Protocol.client_request rocq_file Request.(Status({context})) with
    | Ok(doc) -> Printf.printf "%s%!" doc
  in
  let term = Term.(const run $ context_lines $ rocq_file) in
  Cmd.(make (info "status" ~version ~doc) term)

let step_count =
  let doc =
    "Indicates the number of items $(docv) that should be stepped over (it \
     is equal to 1 by default)."
  in
  Arg.(value & opt int 1 & info ["n"; "count-items"] ~doc ~docv:"NUM")

let steps_cmd =
  let doc =
    "Step over the given number of document items (commands or blanks) in \
     the Rocq document. The command can fail if one of the items cannot be \
     processed successfully. In that case, the cursor is moved to just before \
     the failing item."
  in
  let run count rocq_file =
    match Protocol.client_request rocq_file Request.(Steps({count})) with
    | Ok(real_count) ->
      if real_count < count then
        Printf.printf "Warning: Only %i < %i steps were executed before reaching the end of the file.\n\n" real_count count
    | Error(s, i) ->
        panic "Failed after processing %i items.\nError: %s." i s
  in
  let term = Term.(map with_auto_print (const run $ step_count) $ rocq_file) in
  Cmd.(make (info "steps" ~version ~doc) term)

let command_text =
  let doc =
    "Specifies a chunk of Rocq code $(docv) to insert into the document. If \
     it is not given, then the chunk of text is read from standard input"
  in
  Arg.(value & opt (some string) None & info ["t"; "text"] ~doc ~docv:"TEXT")

let insert_keep =
  let keep =
    Arg.enum [
      ("atomic", Request.Atomic);
      ("succeeding", Request.Succeeding);
      ("all", Request.All);
    ]
  in
  let doc =
    "Controls which inserted items are kept if processing fails: \
     $(b,atomic) rolls back the whole insertion, $(b,succeeding) keeps only \
     the items processed successfully, and $(b,all) keeps all inserted items \
     even if some cannot be processed."
  in
  Arg.(value & opt keep Request.Atomic & info ["keep"] ~doc ~docv:"MODE")

let insert_cmd =
  let doc =
    "Insert the given chunk of Rocq code in the document, at the cursor. The \
     insertion is atomic by default: if any inserted item cannot be processed, \
     no inserted item is kept. The $(b,--keep) option controls what remains \
     after such failures. The command will return a non-zero exit code if any \
     of the insert code cannot be processed."
  in
  let run keep text rocq_file =
    let text =
      match text with Some(text) -> text | None ->
      In_channel.input_all stdin
    in
    match Protocol.client_request rocq_file Request.(Insert({text; keep})) with
    | Ok(()) -> ()
    | Error(s, left) -> panic "Error: could not process suffix %S.\n%s" left s
  in
  let term =
    Term.(map with_auto_print
      (const run $ insert_keep $ command_text) $ rocq_file)
  in
  Cmd.(make (info "insert" ~version ~doc) term)

let query_text =
  let doc =
    "Specifies the Rocq query to be run at the cursor."
  in
  Arg.(value & opt (some string) None & info ["t"; "text"] ~doc ~docv:"TEXT")

let query_cmd =
  let doc =
    "Executes the given Rocq query at the current cursor $(b,without) \
     inserting the query it into the document. Prints the resulting $(b,info) \
     and $(b,notice) feedback to standard output."
  in
  let run text rocq_file =
    let text =
      match text with Some(text) -> text | None ->
      In_channel.input_all stdin
    in
    match Protocol.client_request rocq_file Request.(Query({text})) with
    | Ok(s) -> Printf.printf "%s\n%!" s
    | Error(s, ()) -> panic "Error: %s." s
  in
  let term = Term.(const run $ query_text $ rocq_file) in
  Cmd.(make (info "query" ~version ~doc) term)

let deleted_item_count =
  let doc =
    "Indicates the number of items $(docv) that should be deleted after the \
     cursor (it is equal to 1 by default)."
  in
  Arg.(value & opt int 1 & info ["n"; "count-items"] ~doc ~docv:"NUM")

let delete_cmd =
  let doc =
    "Delete the given number of items (blanks or commands) after the cursor. \
     The cursor is not moved in the operation."
  in
  let run count rocq_file =
    match Protocol.client_request rocq_file Request.(Delete({count})) with
    | Ok(()) -> ()
    | Error(s, ()) -> panic "Error: %s." s
  in
  let term = Term.(map with_auto_print (const run $ deleted_item_count) $ rocq_file) in
  Cmd.(make (info "delete" ~version ~doc) term)

let commit_cmd =
  let doc =
    "Commit the current state of the document to the source file."
  in
  let run rocq_file =
    match Protocol.client_request rocq_file Request.Commit with
    | Ok(()) -> ()
    | Error(s, ()) -> panic "Error: unable to commit.\n%s" s
  in
  let term = Term.(const run $ rocq_file) in
  Cmd.(make (info "commit" ~version ~doc) term)

let goals_cmd =
  let doc =
    "Print the current proof state of the document, including the list of \
     the goals currently in focus."
  in
  let run rocq_file =
    match Protocol.client_request rocq_file Request.Goals with
    | Ok(s) -> Printf.printf "%s%!" s
  in
  let term = Term.(const run $ rocq_file) in
  Cmd.(make (info "goals" ~version ~doc) term)

let backwards_count =
  let doc =
    "Indicates the number of items $(docv) that the cursor should move \
     backwards (it is equal to 1 by default)."
  in
  Arg.(value & opt int 1 & info ["n"; "count-items"] ~doc ~docv:"NUM")

let backwards_cmd =
  let doc =
    "Moves the cursor backwards by the given number of document items \
     (commands or blanks) in the Rocq document."
  in
  let run count rocq_file =
    match Protocol.client_request rocq_file Request.(Backwards({count})) with
    | Ok(()) -> ()
    | Error(s, ()) -> panic "Error: %s." s
  in
  let term = Term.(map with_auto_print (const run $ backwards_count) $ rocq_file) in
  Cmd.(make (info "backwards" ~version ~doc) term)

let goto_pos =
  let position =
    let parse s =
      match String.split_on_char ':' s with
      | [line] ->
          begin
            match int_of_string_opt line with
            | None ->
                Error(`Msg("The line number must be an integer."))
            | Some(line) when line < 1 ->
                Error(`Msg("The line number should be at least 1."))
            | Some(line) ->
                Ok(line, None)
          end
      | [line; col] ->
          begin
            match int_of_string_opt line with
            | None -> Error(`Msg("The line number must be an integer."))
            | Some(line) when line < 1 ->
                Error(`Msg("The line number should be at least 1."))
            | Some(line) ->
            match int_of_string_opt col with
            | None -> Error(`Msg("The column number must be an integer."))
            | Some(col) when col < 1 ->
                Error(`Msg("The column number should be at least 1."))
            | Some(col) -> Ok(line, Some(col))
          end
      | _ -> Error(`Msg("Format must be LINE or LINE:COLUMN."))
    in
    let print ff (line, col) =
      Format.fprintf ff "%i" line;
      Option.iter (Format.fprintf ff ":%i") col
    in
    Arg.conv (parse, print)
  in
  let doc = "Specifies the target position as $(docv)." in
  Arg.(required & opt (some position) None &
    info ["p"; "position-line-column"] ~doc ~docv:"LINE[:COLUMN]")

let goto_cmd =
  let doc =
    "Moves the cursor to the item identified by the given line and column \
     numbers."
  in
  let run (line, col) rocq_file =
    match Protocol.client_request rocq_file Request.(Goto({line; col})) with
    | Ok(()) -> ()
    | Error(s, i) -> panic "Error: %s.\nThe cursor is now at index %i." s i
  in
  let term = Term.(map with_auto_print (const run $ goto_pos) $ rocq_file) in
  Cmd.(make (info "goto" ~version ~doc) term)

let main_man = [
  `S Manpage.s_description;
  `P "$(b,rocq-ed) is a command-line editor for Rocq source files. It \
      operates as a per-file daemon: $(b,rocq-ed init) starts a background \
      session that holds an in-memory representation of a Rocq source file, \
      and subsequent $(b,rocq-ed) invocations talk to that session to \
      inspect or modify it. The session is terminated with \
      $(b,rocq-ed stop).";

  `S "DOCUMENT MODEL";
  `P "The session-managed $(i,document) is the editable, in-memory \
      representation of a Rocq source file. It is structured as a sequence \
      of $(i,items), each of which is either a single Rocq $(i,command) or \
      a chunk of $(i,blanks) (whitespace and Rocq comments).";
  `P "The document carries a $(i,cursor) that splits its items into two \
      parts. The $(i,prefix) holds items that have already been processed \
      by the underlying Rocq top-level: commands in the prefix have been \
      replayed by Rocq and contribute to the current proof state. The \
      $(i,suffix) holds items that belong to the document but have not yet \
      been processed. Most operations either advance the cursor forward \
      through the suffix (such as $(b,steps) and $(b,goto)) or move it \
      backward into the prefix (such as $(b,backwards)).";
  `P "Editing then proceeds by combining cursor movements with \
      $(b,rocq-ed insert), which adds new items at the cursor and attempts \
      to step over them, and $(b,rocq-ed delete), which removes items from \
      the suffix. The current contents of the document, with the cursor \
      displayed as $(b,<CURSOR>), can be inspected at any time with \
      $(b,rocq-ed status). The final state can be written back to disk \
      with $(b,rocq-ed commit). On $(b,rocq-ed init), the document is \
      initialized with the contents of the source file loaded as \
      unprocessed items in the suffix, with the cursor at the beginning.";

  `S "BLANK CHARACTERS";
  `P "Because the document must remain a syntactically valid Rocq source \
      at all times, blank characters between commands are not inserted \
      implicitly: the caller is responsible for providing them. After a \
      dot-terminated command, Rocq requires at least one whitespace \
      character (space, tab, carriage return, or newline) before the next \
      command can start. Inserting $(b,\"Check 1.\") directly after such a \
      command will therefore fail; the inserted text must itself start \
      with the required blanks, e.g. $(b,\" Check 1.\"). A comment alone \
      does not satisfy this requirement; an actual whitespace character \
      is needed.";
  `P "Blanks are themselves first-class items of the document. They appear \
      at their position in the output of $(b,rocq-ed status), and they \
      can be traversed by cursor movements or deleted just like commands.";
]

let _ =
  let cmds =
    [ init_cmd; stop_cmd; status_cmd; steps_cmd; insert_cmd; query_cmd;
      delete_cmd; commit_cmd; goals_cmd; backwards_cmd; goto_cmd ]
  in
  let default = Term.(ret (const (`Help(`Pager, None)))) in
  let default_info =
    let doc =
      "Command line Rocq editor."
    in
    Cmd.info "rocq-ed" ~version ~doc ~man:main_man
  in
  exit (Cmd.eval (Cmd.group default_info ~default cmds))

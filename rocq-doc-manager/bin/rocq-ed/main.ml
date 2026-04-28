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

let no_build =
  let doc =
    "Disables the building of dependencies before starting the editor. This \
     option can be used to speed up the start-up in big projects, when the \
     user knows that dependencies are up-to-date."
  in
  Arg.(value & flag & info ["no-build"] ~doc)

let jobs =
  let doc =
    "Indicates that no more than $(docv) concurrent jobs should be run by \
     $(b,dune) when building dependencies. If $(b,--no-build) is given, this \
     option is a no-op."
  in
  Arg.(value & opt (some int) None & info ["j"; "jobs"] ~doc ~docv:"JOBS")

let display =
  let display =
    let enum = ["progress"; "quiet"; "short"; "verbose"] in
    Arg.enum (List.map (fun m -> (m, m)) enum)
  in
  let doc =
    "Controls the display mode of $(b,dune) when building the dependencies \
     of the file to be processed. If $(b,--no-build) is given, this option \
     is a no-op. Available values are: $(b,progress) (updated status line), \
     $(b,quiet) (only warnings and errors are displayed), $(b,short) (adds \
     one line per command), and $(b,verbose) (full command line is printed)."
  in
  let i = Arg.info ["display"] ~docv:"MODE" ~doc in
  Arg.(value & opt display "progress" & i)

let dune_config =
  let build no_build jobs display = Dune_util.{no_build; jobs; display} in
  Term.(const build $ no_build $ jobs $ display)

let init_cmd =
  let doc =
    "Starts a CLI editor session for the given Rocq source file. Note that \
     when a session for a given source file is running, no other session can \
     be started on the same file."
  in
  let term = Term.(const Protocol.init $ dune_config $ rocq_file) in
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
  Arg.(value & opt (some int) None & info ["C"; "context"] ~doc ~docv:"NUM")

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
    "Indicates the number of steps $(docv) that should be run (it is equal \
     to 1 by default)."
  in
  Arg.(value & opt int 1 & info ["n"; "count"] ~doc ~docv:"NUM")

let steps_cmd =
  let doc =
    "Step over the given number of document items (commands or blanks) in \
     the Rocq document."
  in
  let run count rocq_file =
    match Protocol.client_request rocq_file Request.(Steps({count})) with
    | Ok(()) -> ()
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

let insert_cmd =
  let doc =
    "Insert the given chunk of Rocq code in the document, at the cursor. The \
     cursor is advanced past the inserted chunk."
  in
  let run text rocq_file =
    let text =
      match text with Some(text) -> text | None ->
      In_channel.input_all stdin
    in
    match Protocol.client_request rocq_file Request.(Insert({text})) with
    | Ok(()) -> ()
    | Error(s, left) -> panic "Error: could not process suffix %S.\n%s" left s
  in
  let term = Term.(map with_auto_print (const run $ command_text) $ rocq_file) in
  Cmd.(make (info "insert" ~version ~doc) term)

let query_text =
  let doc =
    "Specifies the Rocq command to be run at the cursor."
  in
  Arg.(value & opt (some string) None & info ["t"; "text"] ~doc ~docv:"TEXT")

let query_cmd =
  let doc =
    "Runs the given Rocq command at the cursor, and prints the resulting \
     $(b,info) and $(b,notice) feedback to standard output."
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
  Arg.(value & opt int 1 & info ["n"; "count"] ~doc ~docv:"NUM")

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

let undo_count =
  let doc =
    "Indicates the number of steps $(docv) that should be undone (it is \
     equal to 1 by default)."
  in
  Arg.(value & opt int 1 & info ["n"; "count"] ~doc ~docv:"NUM")

let undo_cmd =
  let doc =
    "Rolls back the cursor by the given number of document items (commands \
     or blanks) in the Rocq document."
  in
  let run count rocq_file =
    match Protocol.client_request rocq_file Request.(Undo({count})) with
    | Ok(()) -> ()
    | Error(s, ()) -> panic "Error: %s." s
  in
  let term = Term.(map with_auto_print (const run $ undo_count) $ rocq_file) in
  Cmd.(make (info "undo" ~version ~doc) term)

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
    info ["p"; "pos"] ~doc ~docv:"LINE[:COLUMN]")

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

let _ =
  let cmds =
    [ init_cmd; stop_cmd; status_cmd; steps_cmd; insert_cmd; query_cmd;
      delete_cmd; commit_cmd; goals_cmd; undo_cmd; goto_cmd ]
  in
  let default = Term.(ret (const (`Help(`Pager, None)))) in
  let default_info =
    let doc =
      "Command line Rocq editor."
    in
    Cmd.info "rocq-ed" ~version ~doc
  in
  exit (Cmd.eval (Cmd.group default_info ~default cmds))

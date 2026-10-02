open Stdlib_extra.Extra
open Cmdliner

let version = "dev"

let exits = [
  Cmd.Exit.info 0 ~doc:"on success.";
  Cmd.Exit.info 1 ~doc:"on command/request failures.";
  Cmd.Exit.info 123 ~doc:"on protocol errors (e.g., busy / stopped server).";
  Cmd.Exit.info 124 ~doc:"on command-line parsing error.";
  Cmd.Exit.info 125 ~doc:"on unexpected internal errors (bugs).";
]

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

let no_daemon =
  let doc =
    "When this option is specified, $(b,rocq-ed) will not detach to become a \
     daemon, and logging output will be printed to the terminal."
  in
  Arg.(value & flag & info ["D"; "no-daemon"] ~doc)

let init_cmd =
  let doc =
    "Starts a fresh CLI editor session for the given Rocq source file. By \
     default, the session's process is detached to run as a daemon, and \
     session configuration commands are printed to standard output. As a \
     consequence, one can start the daemon with $(b,eval \\$(rocq-ed init \
     path/to/file.v)) to configure the shell's environment appropriately for \
     interacting with the created session on file $(b,path/to/file.v) in \
     follow-up $(b,rocq-ed) commands. When $(b,--no-daemon) is set, the \
     appropriate environment configuration is still printed to standard \
     output, but one cannot use $(b,eval) since the program does not return \
     until the end of the session. In this case, it is up to the user to \
     set up the environment in a separate shell, or to use $(b,--session-id) \
     with the printed value in follow-up invocations."
  in
  let term =
    Term.(const Protocol.init $ dune_config $ no_daemon $ rocq_file)
  in
  Cmd.(make (info "init" ~version ~exits ~doc) term)

let session_id =
  let env =
    let doc = "Unique identifier for the rocq-ed session." in
    Cmd.Env.info "ROCQED_SESSION_ID" ~doc
  in
  let doc =
    "Specify $(docv) as the target $(b,rocq-ed) session identifier. Note \
     that it is generally preferable to set the $(b,ROCQED_SESSION_ID) \
     environment variable to pass the session identifier. This can be \
     done automatically by starting a session using $(b,eval \\$(rocq-ed \
     init path/to/file.v))."
  in
  let arg =
    Arg.(value & opt (some string) None &
      info ["s"; "session-id"] ~env ~doc ~docv:"ID")
  in
  let check o =
    match o with
    | Some(id) -> Ok(id)
    | None     ->
        Error(`Msg("environment variable ROCQED_SESSION_ID is undefined, so \
          the --session-id option is required"))
  in
  Term.(term_result (const check $ arg))

let stop_cmd =
  let doc = "Stop the session." in
  let term = Term.(const Protocol.stop $ session_id) in
  Cmd.(make (info "stop" ~version ~exits ~doc) term)

let non_negative_int_or_all =
  let parse s =
    match s with "all" -> Ok(None) | _ ->
    match int_of_string_opt s with
    | None    -> Error(`Msg("expected a non-negative integer or \"all\""))
    | Some(i) ->
    if i >= 0 then Ok(Some(i)) else
    Error(`Msg("expected a non-negative integer or \"all\""))
  in
  let print ff v =
    match v with
    | None    -> Format.fprintf ff "all"
    | Some(i) -> Format.fprintf ff "%i" i
  in
  Arg.conv (parse, print)

let context =
  let parse s =
    match s with
    | "none" -> Ok(Request.No_context)
    | "all"  -> Ok(Request.All_context)
    | s      ->
    match int_of_string_opt s with
    | None    -> Error(`Msg("expected an integer, \"all\", or \"none\""))
    | Some(i) ->
    if i >= 0 then Ok(Request.Context_lines(i)) else
    Error(`Msg("expected a non-negative integer, \"all\", or \"none\""))
  in
  let print ff v =
    match v with
    | Request.No_context       -> Format.fprintf ff "none"
    | Request.All_context      -> Format.fprintf ff "all"
    | Request.Context_lines(i) -> Format.fprintf ff "%i" i
  in
  Arg.conv (parse, print)

let context_lines =
  let doc =
    "Control how much document context is printed. A non-negative integer \
     specifies how many lines are printed before and after the cursor. Use \
     $(b,all) to print the whole Rocq document, or $(b,none) to disable \
     context printing. The default is 5. This option cannot be combined \
     with $(b,--json)."
  in
  Arg.(value & opt (some context) None &
    info ["C"; "context-lines"] ~doc ~docv:"NUM|all|none")

let print_goals =
  let doc =
    "Print the open proof goals at the cursor after running the command, but \
     before any potential rollback, even when document processing fails. No \
     printing is done in case of invalid argument for the command."
  in
  Arg.(value & flag & info ["G"; "print-goals"] ~doc)

let print_context =
  let doc =
    "Print document context after running the command, but before any \
     potential rollback, including when document processing fails. A \
     non-negative integer specifies how many lines are printed before and \
     after the cursor. Use $(b,all) to print the whole document, or \
     $(b,none) to disable context printing. The default is $(b,none). If \
     $(b,--print-context) is given without argument it defaults to $(b,5). \
     No printing is done in case of invalid argument for the command."
  in
  let vopt = Request.Context_lines(5) in
  Arg.(value & opt ~vopt context Request.No_context &
    info ["C"; "print-context"] ~docv:"NUM|all|none" ~doc)

let print_after =
  let make context goals = Request.{context; goals} in
  Term.(const make $ print_context $ print_goals)

let output_after_error s =
  match s with "" -> "" | _ ->
  let len = String.length s in
  "\n\n" ^ if s.[len - 1] = '\n' then String.sub s 0 (len - 1) else s

let status_json =
  let doc =
    "Print a JSON object containing item lists for the processed prefix and \
     unprocessed suffix, plus the current structured proof goals, if any."
  in
  Arg.(value & flag & info ["json"] ~doc)

let status_goals =
  let doc =
    "Print the current proof goals at the cursor. This option cannot be \
     combined with $(b,--json), whose output already includes structured \
     goals."
  in
  Arg.(value & flag & info ["goals"] ~doc)

let status_mode =
  let make context goals json =
    match (json, goals, context) with
    | (true , true , _      ) ->
        Error(`Msg("'--goals' and '--json' cannot be used together"))
    | (true , _    , Some(_)) ->
        Error(`Msg("'--context-lines' and '--json' cannot be used together"))
    | (true , false, None   ) ->
        Ok(`JSON)
    | (false, _    , _      ) ->
    let context =
      let default = Request.Context_lines(5) in
      Stdlib.Option.value context ~default
    in
    Ok(`Text(Request.{context; goals}))
  in
  Term.(term_result (const make $ context_lines $ status_goals $ status_json))

let status_cmd =
  let doc =
    "Print the current contents of the Rocq document, including the position \
     of the cursor marked as $(b,<CURSOR>), and optionally the open goals at \
     the cursor. With $(b,--json), print the document prefix and suffix as \
     item lists, together with the current structured goals, as JSON instead."
  in
  let run mode id =
    let Ok(doc) = Protocol.client_request id (Request.Status({mode})) in
    Printf.printf "%s%!" doc
  in
  let term = Term.(const run $ status_mode $ session_id) in
  Cmd.(make (info "status" ~version ~exits ~doc) term)

let step_count =
  let doc =
    "Indicates the number of items $(docv) that should be stepped over (it \
     is equal to 1 by default). Use $(b,all) to step all the way to the end \
     of the file."
  in
  let docv = "NUM|all" in
  Arg.(value & opt non_negative_int_or_all (Some(1)) &
    info ["n"; "count-items"] ~doc ~docv)

let steps_cmd =
  let doc =
    "Step over the given number of document items (commands or blanks) in \
     the Rocq document. The command can return a non-zero exit code if one \
     of the items cannot be  processed successfully. In that case, the \
     cursor is moved to just before the failing item."
  in
  let run count print id =
    let ((data, output), res) =
      Protocol.full_client_request id Request.(Steps({count; print}))
    in
    Request.print_feedback data;
    match res with
    | Error(s, count) ->
        panic "Failed after processing %i items.\nError: %s.%s" count s
          (output_after_error output)
    | Ok(real_count) ->
    let check_count count =
      if real_count < count then
        Printf.printf "Warning: Only %i < %i steps were executed before \
          reaching the end of the file.\n\n" real_count count
    in
    Option.iter check_count count;
    Printf.printf "%s%!" output
  in
  let term = Term.(const run $ step_count $ print_after $ session_id) in
  Cmd.(make (info "steps" ~version ~exits ~doc) term)

let command_text =
  let doc =
    "Specifies a chunk of Rocq code $(docv) to insert into the document. If \
     it is not given, then the chunk of text is read from standard input. \
     Leading / trailing white spaces may be required (see $(b,rocq-ed \
     --help) for details)."
  in
  Arg.(value & opt (some string) None & info ["t"; "text"] ~doc ~docv:"TEXT")

let insert_keep =
  let keep =
    Arg.enum [
      ("atomic", `Atomic);
      ("successful", `Successful);
      ("all", `All);
      ("none", `None);
    ]
  in
  let doc =
    "Controls which inserted items are kept: $(b,atomic) either succeeds at \
     inserting all items or rolls back any change, $(b,successful) keeps the \
     prefix of items that were inserted successfully and discards remaining \
     ones, $(b,all) inserts all items but adds any failing suffix after the \
     cursor, and $(b,none) always rolls back any change and only checks \
     whether the items could be inserted successfully."
  in
  Arg.(value & opt keep `Atomic & info ["k"; "keep"] ~doc ~docv:"MODE")

let insert_cmd =
  let doc =
    "Insert the given chunk of Rocq code in the document, at the cursor. The \
     insertion is atomic by default: if any inserted item cannot be \
     processed, no inserted item is kept. The $(b,--keep) option controls \
     what remains after such failures. The command will return a non-zero \
     exit code if any of the insert code cannot be processed."
  in
  let run keep text print id =
    let text =
      match text with Some(text) -> text | None ->
      In_channel.input_all stdin
    in
    let req = Request.(Insert({text; keep; print})) in
    let ((data, output), res) = Protocol.full_client_request id req in
    Request.print_feedback data;
    match res with
    | Ok(()) -> Printf.printf "%s%!" output
    | Error(s, Request.{remaining; unchanged}) ->
        let unchanged =
          if unchanged then "\nThe document is unchanged." else ""
        in
        panic "Error: could not process suffix %S.\n%s%s%s"
          remaining s unchanged (output_after_error output)
  in
  let term =
    Term.(const run $ insert_keep $ command_text $ print_after $ session_id)
  in
  Cmd.(make (info "insert" ~version ~exits ~doc) term)

let deleted_item_count =
  let doc =
    "Indicates the number of items $(docv) that should be deleted after the \
     cursor (it is equal to 1 by default)."
  in
  Arg.(value & opt non_negative_int_or_all (Some(1)) &
    info ["n"; "count-items"] ~doc ~docv:"NUM")

let delete_cmd =
  let doc =
    "Delete the given number of items (blanks or commands) after the cursor. \
     The cursor is not moved in the operation."
  in
  let run count print id =
    let (output, res) =
      Protocol.full_client_request id Request.(Delete({count; print}))
    in
    match res with
    | Ok(()) -> Printf.printf "%s%!" output
    | Error(s, ()) -> panic "Error: %s.%s" s (output_after_error output)
  in
  let term =
    Term.(const run $ deleted_item_count $ print_after $ session_id)
  in
  Cmd.(make (info "delete" ~version ~exits ~doc) term)

let commit_file =
  let doc =
    "Write the document to $(docv) instead of the source file (a snapshot). \
     The session keeps targeting the source file."
  in
  Arg.(value & opt (some string) None & info ["file"] ~doc ~docv:"PATH")

let commit_include_suffix =
  let doc =
    "Include the unprocessed suffix (items after the cursor). By default the \
     suffix is excluded since it was not checked by Rocq."
  in
  Arg.(value & flag & info ["a"; "include-suffix"] ~doc)

let commit_force =
  let doc =
    "Force the commit of the document even if there are unprocessed items \
     after the cursor, and $(b,--include-suffix) was not used."
  in
  Arg.(value & flag & info ["f"; "force"] ~doc)

let commit_cmd =
  let doc =
    "Commits the processed prefix of the document to the file system. Unless \
     $(b,--force) or $(b,--include-suffix) is used, the command fail when \
     there are unprocesed item after the cursor."
  in
  let run file force include_suffix id =
    let req = Request.(Commit({file; force; include_suffix})) in
    match Protocol.client_request id req with
    | Error(s, ()) -> panic "Error: unable to commit.\n%s" s
    | Ok(()) -> ()
  in
  let term =
    Term.(const run $ commit_file $ commit_force $ commit_include_suffix $
      session_id)
  in
  Cmd.(make (info "commit" ~version ~exits ~doc) term)

let goals_cmd =
  let doc =
    "Print the current proof state of the document, including the list of \
     the goals currently in focus."
  in
  let run id =
    let Ok(s) = Protocol.client_request id Request.Goals in
    Printf.printf "%s%!" s
  in
  let term = Term.(const run $ session_id) in
  Cmd.(make (info "goals" ~version ~exits ~doc) term)

let backwards_count =
  let doc =
    "Indicates the number of items that the cursor should be moved over \
     backwards in the document. It is equal to 1 by default, and $(b,all) \
     can be used to move the cursor to the start of the document."
  in
  Arg.(value & opt non_negative_int_or_all (Some(1)) &
    info ["n"; "count-items"] ~doc ~docv:"NUM|all")

let backwards_cmd =
  let doc =
    "Moves the cursor backwards over the given number of items (commands or \
     blanks) in the Rocq document. Said otherwise, the given number of items \
     are moved from the (processed) prefix of the document to its \
     (unprocessed) suffix."
  in
  let run count print id =
    let (output, res) =
      Protocol.full_client_request id Request.(Backwards({count; print}))
    in
    match res with
    | Ok(()) -> Printf.printf "%s%!" output
    | Error(s, ()) -> panic "Error: %s.%s" s (output_after_error output)
  in
  let term = Term.(const run $ backwards_count $ print_after $ session_id) in
  Cmd.(make (info "backwards" ~version ~exits ~doc) term)

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
  let run (line, col) print id =
    let (output, res) =
      Protocol.full_client_request id Request.(Goto({line; col; print}))
    in
    match res with
    | Ok(()) -> Printf.printf "%s%!" output
    | Error(s, None) ->
        panic "Error: %s.%s" s (output_after_error output)
    | Error(s, Some(line, col)) ->
        panic "Error: failed to process the item at line %i, column %i.\n%s%s"
          line col s (output_after_error output)
  in
  let term = Term.(const run $ goto_pos $ print_after $ session_id) in
  Cmd.(make (info "goto" ~version ~exits ~doc) term)

let main_man = [
  `S Manpage.s_description;
  `P "$(b,rocq-ed) is a command-line editor for Rocq source files. An editor \
      session is created by $(b,rocq-ed init path/to/file.v), which starts \
      a server process holding an in-memory representation of the given Rocq \
      source file. Subsequent $(b,rocq-ed) invocations are used to interact \
      with the server, querying or editing the state of the Rocq source file
      in memory, and potentially committing changes back to disk. A session \
      is terminated via $(b,rocq-ed stop).";

  `S "SESSION IDENTIFIER";
  `P "A $(b,rocq-ed) session is identified by a unique session identifier, \
      created at $(b,rocq-ed init) and printed to the shell. The identifier \
      must be provided for subsequent interactions, either using the \
      $(b,--session-id) argument, or by setting environment variable \
      $(b,ROCQED_SESSION_ID). Note that $(b,eval \\$(rocq-ed init \
      path/to/file.v)) can be used to set up the environment variable in the \
      current shell when creating a session. However, this only works when \
      the session process is daemonized (which is the default), and not when \
      $(b,--no-daemon) is used.";

  `S "DOCUMENT MODEL";
  `P "The session-managed $(i,document) is the editable, in-memory \
      representation of a Rocq source file. It is structured as a sequence \
      of $(i,items), each of which is either a single Rocq $(i,command) or \
      a chunk of $(i,blanks) (white spaces and Rocq comments).";
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

  `S "EDITING WORKFLOW";
  `P "For interactive Rocq source edits, $(b,rocq-ed) is usually a better \
      edit/query loop than repeatedly invoking $(b,dune build file.vo). \
      $(b,rocq-ed init) obtains the Rocq command-line arguments from Dune \
      and builds dependencies by default; $(b,--no-build-deps) is an \
      explicit opt-out for cases where dependencies are already known to \
      be current.";
  `P "Once initialized, the server maintains an editor session. Cursor \
      movement, queries, edits, and proof-state inspection can reuse the \
      already-processed prefix instead of restarting the whole Dune target \
      each time. Use normal composed Dune builds afterwards for final \
      validation.";

  `S "BLANK CHARACTERS";
  `P "Appropriate chunks of blank characters formed of white spaces and \
      Rocq comments must be explicitly inserted by the user in between Rocq \
      commands, so that the document remains syntactically valid as a Rocq \
      source file. Blank characters are never automatically inserted by \
      $(b,rocq-ed).";
  `P "A chunk of blank characters counts as its own item in the document,
      and it can be inserted and deleted just like a Rocq command. Two items \
      each containing a chunk of blank characters may appear next to \
      each-other in the document: they are not automatically combined.";
  `P "The user should pay close attention to the items immediately \
      surrounding the cursor when inserting a chunk of text. Indeed, \
      leading/trailing spaces may be required for the inserted text not to \
      interfere with the surrounding items. For example, if the cursor is at \
      the end of the document and immediately follows item \
      $(b,\"Check 0.\"), then inserting $(b,\"Check 1.\") fails because it \
      would produce $(b,\"Check 0.Check 1.\") (which is a syntax error). \
      Inserting additional blanks using $(b,\" Check 1.\") avoids the issue.";

  `S "QUERYING ROCQ";
  `P "In addition to inspecting the proof state using $(b,rocq-ed goals), \
      arbitrary Rocq queries can be run with $(b,rocq-ed insert --keep=none) \
      since it does not persist any change to the document. For example, to \
      query the definition of a function $(b,f) together with a list of all \
      available lemmas about it, one can use $(b,rocq-ed insert --keep=none \
      --text=' About f. Search f. '). Although no changes are persisted to \
      the document, the user must ensure that the text is insertable at the \
      cursor. In particular, appropriate blank characters should be included \
      as per the previous section.";

  `S "COMMAND FAILURES";
  `P "All commands except $(b,init) and $(b,stop) can fail without affecting \
      the health of the rocq-ed session. It is not necessary to restart the \
      session when any of the other commands fail";
]

let _ =
  let cmds =
    [ init_cmd; stop_cmd; status_cmd; steps_cmd; insert_cmd; delete_cmd;
      commit_cmd; goals_cmd; backwards_cmd; goto_cmd ]
  in
  let default = Term.(ret (const (`Help(`Pager, None)))) in
  let default_info =
    let doc = "Command line Rocq editor." in
    Cmd.info "rocq-ed" ~version ~exits ~doc ~man:main_man
  in
  exit (Cmd.eval (Cmd.group default_info ~default cmds))

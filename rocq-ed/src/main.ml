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
    "Disable the building of dependencies before starting the editor. This \
     option can speed up start-up in large projects when dependencies are \
     known to be up-to-date. WARNING: stale dependencies can cause failures \
     or false successes."
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
    "Run the server in the foreground instead of detaching it as a daemon. \
     Logging output is printed to the terminal, and the command does not \
     return until the session is stopped."
  in
  Arg.(value & flag & info ["D"; "no-daemon"] ~doc)

let init_cmd =
  let doc =
    "Start a fresh command-line editor session for the given Rocq source \
     file. By default, the server detaches to run as a daemon and prints an \
     $(b,export) command for $(b,ROCQED_SESSION_ID). In a POSIX-compatible \
     shell, pass the output of $(b,rocq-ed) $(b,init) to $(b,eval) to start \
     the daemon and configure the current shell. With $(b,--no-daemon), the \
     server remains in the foreground until the session is stopped and \
     prints $(b,ROCQED_SESSION_ID=ID). Because the command does not return, \
     it cannot be passed to $(b,eval). Instead, pass the identifier to \
     follow-up commands or export the assignment in a separate shell."
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
    "Use $(docv) as the target $(b,rocq-ed) session identifier. It is \
     generally preferable to set the $(b,ROCQED_SESSION_ID) environment \
     variable instead. In a POSIX-compatible shell, pass the output from a \
     daemonized $(b,init) command to $(b,eval) to set it automatically."
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
  let doc =
    "Stop the session. Changes that have not been written with the \
     $(b,commit) command are discarded."
  in
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

let print_goals operation =
  let doc =
    match operation with
    | `Insert ->
        "Print the open proof goals after attempting the insertion and \
         before any rollback. Goals are printed after a Rocq processing \
         failure, but not when the insertion is rejected before Rocq \
         processing begins."
    | `Move ->
        "Print the open proof goals after moving the cursor, including when \
         forward processing stops at a failing item. Nothing is printed if \
         the move target is invalid."
    | `Delete ->
        "Print the open proof goals after deleting the requested items. \
         Nothing is printed if the deletion cannot be performed."
  in
  Arg.(value & flag & info ["G"; "print-goals"] ~doc)

let print_context operation =
  let timing =
    match operation with
    | `Insert ->
        "Print document context after attempting the insertion and before \
         any rollback. Context is printed after a Rocq processing failure, \
         but not when the insertion is rejected before Rocq processing \
         begins."
    | `Move ->
        "Print document context after moving the cursor, including when \
         forward processing stops at a failing item. Nothing is printed if \
         the move target is invalid."
    | `Delete ->
        "Print document context after deleting the requested items. Nothing \
         is printed if the deletion cannot be performed."
  in
  let doc =
    timing ^ " A non-negative integer specifies how many lines are printed \
     before and after the cursor. Use $(b,all) to print the whole document, \
     or $(b,none) to disable context printing. The default is $(b,none). If \
     $(b,--print-context) is given without an argument, it defaults to \
     $(b,5)."
  in
  let vopt = Request.Context_lines(5) in
  Arg.(value & opt ~vopt context Request.No_context &
    info ["C"; "print-context"] ~docv:"NUM|all|none" ~doc)

let print_after operation =
  let make context goals = Request.{context; goals} in
  Term.(const make $ print_context operation $ print_goals operation)

let feedback =
  let default = Feedback.[Notice; Warning] in
  let names =
    (Feedback.Debug, "debug") :: (Feedback.Info, "info") ::
      (Feedback.Notice, "notice") :: (Feedback.Warning, "warning") :: []
  in
  let components =
    let make (l, s) =
      Either.[(s, Left(l)); ("+"^s, Right(true,l)); ("-"^s, Right(false,l))]
    in
    List.concat_map make names
  in
  let parse s =
    match s with
    | "all" -> Ok(List.map fst names)
    | "none" -> Ok([])
    | _ ->
    let items = String.split_on_char ',' s in
    let find acc item =
      match acc with Error(_) -> acc | Ok(items) ->
      match List.assoc_opt item components with
      | None -> Error(item)
      | Some(item) -> Ok(item :: items)
    in
    match List.fold_left find (Ok([])) items with
    | Error(item) ->
        Error(`Msg(Printf.sprintf "invalid feedback selector %S (expected \
          all, none, LEVEL, +LEVEL, or -LEVEL)" item))
    | Ok(items) ->
    let apply_selectors sels levels =
      let add acc (enable, level) =
        let acc = List.filter (fun l -> l <> level) acc in
        if enable then level :: acc else acc
      in
      List.fold_left add levels sels
    in
    match List.partition_map Fun.id (List.rev items) with
    | (items, []  ) -> Ok(items)
    | ([]   , sels) -> Ok(apply_selectors sels default)
    | (_    , _   ) ->
        Error(`Msg("explicit feedback levels cannot be mixed with +LEVEL or \
          -LEVEL selectors"))
  in
  let print ff levels =
    let pp ff level = Format.pp_print_string ff (List.assoc level names) in
    let levels = List.sort_uniq Stdlib.compare levels in
    match List.length levels with
    | 0 -> Format.pp_print_string ff "none"
    | 4 -> Format.pp_print_string ff "all"
    | _ ->
    let pp_sep ff () = Format.pp_print_string ff "," in
    Format.pp_print_list ~pp_sep pp ff levels
  in
  let doc =
    "Controls which Rocq feedback messages are printed while processing \
     commands. Values $(b,all) and $(b,none) respectively enable or disable \
     all configurable feedback levels. A comma-separated list of $(b,LEVEL)s \
     can be used to enable exactly those levels, and a comma-separated list \
     of selectors of the form $(b,+LEVEL) or $(b,-LEVEL) modifies the \
     default of $(b,notice,warning). Available $(b,LEVEL)s are $(b,debug), \
     $(b,info), $(b,notice), and $(b,warning). For example, using \
     $(b,--feedback=+info,-warning) is equivalent to \
     $(b,--feedback=notice,info)."
  in
  Arg.(value & opt (Arg.conv (parse, print)) default &
    info ["feedback"] ~docv:"SPEC" ~doc)

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
    "Print document context around the cursor, which is marked as \
     $(b,<CURSOR>), and optionally print the open goals. By default, up to \
     five lines before and after the cursor are shown; use \
     $(b,--context-lines=all) for the whole document. With $(b,--json), \
     print the complete document prefix and suffix as item lists, together \
     with the current structured goals, as JSON instead."
  in
  let run mode id =
    let Ok(doc) = Protocol.client_request id (Request.Status({mode})) in
    Printf.printf "%s%!" doc
  in
  let term = Term.(const run $ status_mode $ session_id) in
  Cmd.(make (info "status" ~version ~exits ~doc) term)

let move_pos =
  let position =
    let parse s =
      match String.split_on_char ':' s with
      | [line] ->
          begin
            match int_of_string_opt line with
            | None -> Error(`Msg("The line number must be an integer."))
            | Some(line) when line < 1 ->
                Error(`Msg("The line number should be at least 1."))
            | Some(line) -> Ok(Request.Position({line; col = None}))
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
            | Some(col) -> Ok(Request.Position({line; col = Some(col)}))
          end
      | _ -> Error(`Msg("Format must be LINE or LINE:COLUMN."))
    in
    let print ff target =
      match target with
      | Request.Position({line; col}) ->
          Format.fprintf ff "%i" line;
          Option.iter (Format.fprintf ff ":%i") col
      | _ -> assert false
    in
    Arg.conv (parse, print)
  in
  let doc =
    "Move to the item at the specified source position. Line and column \
     numbers are one-based. If $(b,COLUMN) is omitted, move to the first \
     item on $(b,LINE)."
  in
  Arg.(value & opt (some position) None &
    info ["p"; "position-line-column"] ~doc ~docv:"LINE[:COLUMN]")

let move_item =
  let item =
    let error () =
      Error(`Msg("expected NUM, +NUM, -NUM, +all, or -all"))
    in
    let non_negative s make =
      match int_of_string_opt s with
      | Some(i) when i >= 0 -> Ok(make i)
      | None | Some(_) -> error ()
    in
    let parse s =
      match s with
      | "+all" -> Ok(Request.Relative(Request.Forward, None))
      | "-all" -> Ok(Request.Relative(Request.Backward, None))
      | _ when String.starts_with ~prefix:"+" s ->
          let value = String.sub s 1 (String.length s - 1) in
          non_negative value
            (fun i -> Request.Relative(Request.Forward, Some(i)))
      | _ when String.starts_with ~prefix:"-" s ->
          let value = String.sub s 1 (String.length s - 1) in
          non_negative value
            (fun i -> Request.Relative(Request.Backward, Some(i)))
      | _ -> non_negative s (fun i -> Request.Absolute(i))
    in
    let print ff target =
      match target with
      | Request.Absolute(i) -> Format.fprintf ff "%i" i
      | Request.Relative(Request.Forward, None) ->
          Format.fprintf ff "+all"
      | Request.Relative(Request.Backward, None) ->
          Format.fprintf ff "-all"
      | Request.Relative(Request.Forward, Some(i)) ->
          Format.fprintf ff "+%i" i
      | Request.Relative(Request.Backward, Some(i)) ->
          Format.fprintf ff "-%i" i
      | Request.Position(_) -> assert false
    in
    Arg.conv (parse, print)
  in
  let doc =
    "Move using an item position. $(b,NUM) is an absolute, zero-based cursor \
     position (the number of items before the cursor). $(b,+NUM) and \
     $(b,-NUM) move relative to the current cursor. $(b,+all) moves to the \
     end of the document and $(b,-all) moves to its start."
  in
  Arg.(value & opt (some item) None &
    info ["n"; "item"] ~doc ~docv:"NUM|+NUM|-NUM|+all|-all")

let move_target =
  let make position item =
    match (position, item) with
    | (Some(target), None) | (None, Some(target)) -> Ok(target)
    | (None, None) -> Ok(Request.Relative(Request.Forward, Some(1)))
    | (Some(_), Some(_)) ->
        Error(`Msg("'--position-line-column' and '--item' are incompatible"))
  in
  Term.(term_result (const make $ move_pos $ move_item))

let move_cmd =
  let doc =
    "Move through the document by placing the cursor at another item \
     boundary. The $(b,--position-line-column) option selects a target from \
     a one-based $(b,LINE[:COLUMN]) source position. The $(b,--item) option \
     selects an absolute or relative item position. Moving forward processes \
     the traversed Rocq commands and can fail; the cursor is then left just \
     before the failing item. By default, the cursor moves forward one item, \
     as with $(b,--item=+1)."
  in
  let run target print feedback id =
    let req = Request.(Move({target; print})) in
    let ((data, output), res) = Protocol.full_client_request id req in
    Request.print_feedback feedback data;
    Printf.printf "%s%!" output;
    match res with
    | Error(s, Request.Relative_failure(count)) ->
        if output <> "" then Printf.printf "\n%!";
        panic "Failed after processing %i items.\nError: %s." count s
    | Error(s, Request.Target_failure(None)) ->
        if output <> "" then Printf.printf "\n%!";
        panic "Error: %s." s
    | Error(s, Request.Target_failure(Some(line, col))) ->
        if output <> "" then Printf.printf "\n%!";
        panic "Error: failed to process the item at line %i, column %i.\n%s"
          line col s
    | Ok(real_count) ->
        let warn direction count endpoint =
          match real_count < count with false -> () | true ->
          if output <> "" then Printf.printf "\n%!";
          match direction with
          | Request.Forward ->
              Printf.eprintf "Warning: Only %i < %i steps were executed \
                before reaching the %s of the file.\n%!"
                real_count count endpoint
          | Request.Backward ->
              Printf.eprintf "Warning: Only %i < %i steps were reverted \
                before reaching the %s of the file.\n%!"
                real_count count endpoint
        in
        match target with
        | Request.Relative(Request.Forward, Some(count)) ->
            warn Request.Forward count "end"
        | Request.Relative(Request.Backward, Some(count)) ->
            warn Request.Backward count "start"
        | Request.Relative(_, None)
        | Request.Absolute(_)
        | Request.Position(_) -> ()
  in
  let term =
    Term.(const run $ move_target $ print_after `Move $ feedback $ session_id)
  in
  Cmd.(make (info "move" ~version ~exits ~doc) term)

let command_text =
  let doc =
    "Specify a chunk of Rocq code $(docv) to insert into the document. If it \
     is omitted, the text is read from standard input. Leading or trailing \
     whitespace may be required; see the main $(b,rocq-ed) help page."
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
    "Control which inserted items are kept. $(b,atomic) either processes all \
     items or rolls back the entire insertion. $(b,successful) keeps the \
     successfully processed prefix and discards the remaining inserted \
     items. $(b,all) keeps all parsed items; on a processing failure, the \
     failing item and the remainder are left after the cursor. $(b,none) \
     always rolls back the insertion and only checks whether all items can \
     be processed. A parse failure always leaves the document unchanged."
  in
  Arg.(value & opt keep `Atomic & info ["k"; "keep"] ~doc ~docv:"MODE")

let insert_cmd =
  let doc =
    "Insert the given chunk of Rocq code into the document at the cursor. \
     The insertion is atomic by default: if any inserted item cannot be \
     processed, no inserted item is kept. The $(b,--keep) option controls \
     which items remain and can also make a successful insertion temporary. \
     The command returns a non-zero exit code if the text cannot be parsed \
     or processed completely."
  in
  let run keep text print feedback id =
    let text =
      match text with Some(text) -> text | None ->
      In_channel.input_all stdin
    in
    let req = Request.(Insert({text; keep; print})) in
    let ((data, output), res) = Protocol.full_client_request id req in
    Request.print_feedback feedback data;
    Printf.printf "%s%!" output;
    match res with
    | Ok(()) -> ()
    | Error(s, Request.{remaining; unchanged}) ->
        if output <> "" then Printf.printf "\n%!";
        if unchanged then Printf.printf "The document is unchanged.\n\n%!";
        panic "Error: could not process suffix %S.\n%s" remaining s
  in
  let term =
    Term.(const run $ insert_keep $ command_text $ print_after `Insert $
      feedback $ session_id)
  in
  Cmd.(make (info "insert" ~version ~exits ~doc) term)

let deleted_item_count =
  let doc =
    "Specifies the number of items to be deleted after the cursor, or \
     $(b,all) to delete the whole suffix. By default, only a single item is \
     deleted."
  in
  Arg.(value & opt non_negative_int_or_all (Some(1)) &
    info ["n"; "count-items"] ~doc ~docv:"NUM|all")

let delete_cmd =
  let doc =
    "Delete items (blanks or commands) after the cursor. One item is deleted \
     by default; $(b,--count-items=all) deletes the whole suffix. The cursor \
     is not moved."
  in
  let run count print id =
    let (output, res) =
      Protocol.full_client_request id Request.(Delete({count; print}))
    in
    Printf.printf "%s%!" output;
    match res with
    | Ok(()) -> ()
    | Error(s, ()) ->
        if output <> "" then Printf.printf "\n%!";
        panic "Error: %s." s
  in
  let term =
    Term.(const run $ deleted_item_count $ print_after `Delete $ session_id)
  in
  Cmd.(make (info "delete" ~version ~exits ~doc) term)

let commit_file =
  let doc =
    "Write the committed contents to $(docv) instead of the source file. The \
     session continues to target the original source file."
  in
  Arg.(value & opt (some string) None & info ["file"] ~doc ~docv:"PATH")

let commit_include_suffix =
  let doc =
    "Include the unprocessed suffix (items after the cursor) in the \
     committed contents. This permits a commit with a non-empty suffix \
     without $(b,--force), but the included items have not been checked by \
     Rocq."
  in
  Arg.(value & flag & info ["a"; "include-suffix"] ~doc)

let commit_force =
  let doc =
    "Allow a commit with a non-empty suffix while writing only the processed \
     prefix. This option is unnecessary when $(b,--include-suffix) is used."
  in
  Arg.(value & flag & info ["f"; "force"] ~doc)

let commit_cmd =
  let doc =
    "Write document contents to the source file, or to the path selected by \
     $(b,--file). By default, the command fails if there are unprocessed \
     items after the cursor. Use $(b,--force) to write only the processed \
     prefix despite a non-empty suffix, or $(b,--include-suffix) to also \
     write the unchecked suffix."
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

let main_man = [
  `S Manpage.s_description;
  `P "$(b,rocq-ed) is a command-line editor for Rocq source files. The \
      $(b,init) command starts a server process that holds an in-memory \
      representation of a source file. Subsequent invocations query or edit \
      that representation and can commit changes to disk. The $(b,stop) \
      command terminates the session.";

  `S "SESSION IDENTIFIER";
  `P "The $(b,init) command creates a unique session identifier. Subsequent \
      commands select the session with $(b,--session-id) or with the \
      $(b,ROCQED_SESSION_ID) environment variable. By default, $(b,init) \
      daemonizes the server and prints an $(b,export) command. In a \
      POSIX-compatible shell, the following starts a session and configures \
      the current shell:";
  `Pre "$(b,eval \\$(rocq-ed init path/to/file.v))";
  `P "With $(b,--no-daemon), export the printed assignment in a separate \
      shell or pass the identifier with $(b,--session-id=ID).";

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
      been processed. The $(b,move) command moves the cursor forward or \
      backward to a source-code position or an item position. An item \
      position can be absolute or relative to the current cursor position.";
  `P "Editing combines cursor movements with $(b,insert), which adds and \
      processes new items at the cursor, and $(b,delete), which removes \
      items from the suffix. The $(b,status) command displays context around \
      the cursor, marked as $(b,<CURSOR>). Use $(b,--context-lines=all) to \
      display the whole document. The $(b,commit) command writes changes to \
      disk. At initialization, the source file is loaded as unprocessed \
      items in the suffix, with the cursor at the beginning.";

  `S "EDITING WORKFLOW";
  `P "For interactive Rocq source edits, $(b,rocq-ed) is usually a better \
      edit/query loop than repeated $(b,dune) builds. The $(b,init) command \
      obtains suitable command-line arguments from $(b,dune) and builds \
      dependencies when necessary. Use $(b,--no-build-deps) only when \
      dependencies are known to be up-to-date.";
  `P "Once initialized, the server maintains an editor session. Cursor \
      movements, insertions, queries, and proof-state inspection can reuse \
      the already-processed prefix instead of attempting to build the target \
      from scratch each time. After the end of a $(b,rocq-ed) session, and \
      especially if changes were committed to the Rocq source file, validate \
      that the file can be successfully built by $(b,dune).";

  `S "BLANK ITEMS";
  `P "Chunks of blanks, consisting of whitespace and Rocq comments, must be \
      explicitly inserted between Rocq commands so that the document remains \
      syntactically valid as a Rocq source file. $(b,rocq-ed) never inserts \
      blanks automatically.";
  `P "A chunk of blanks counts as its own item in the document and can be \
      inserted or deleted like a Rocq command. Two blank items may appear \
      next to each other; they are not automatically combined.";
  `P "The user should pay close attention to the items immediately \
      surrounding the cursor when inserting a chunk of text. Leading or \
      trailing whitespace may be required to prevent the inserted text from \
      interfering with the surrounding items. For example, if the cursor is \
      at the end of the document and immediately follows item \
      \"Check 0.\", then inserting \"Check 1.\" fails because it \
      would produce \"Check 0.Check 1.\", which is a syntax error. \
      Inserting the leading blank in \" Check 1.\" avoids the issue.";

  `S "QUERYING ROCQ";
  `P "The $(b,goals) command inspects the proof state. Arbitrary Rocq \
      queries can be run with $(b,insert) and $(b,--keep=none), which does \
      not persist changes. For example, the following queries a function \
      $(b,f) and searches for lemmas about it:";
  `Pre "rocq-ed insert --keep=none --text=' About f. Search f. '";
  `P "The text must be insertable at the cursor and include appropriate \
      blanks, as described in the previous section. The $(b,insert) command \
      does not print $(b,info)-level feedback by default. The user can use \
      $(b,--feedback=+info) for queries that need it.";

  `S "COMMAND FAILURES";
  `P "A command/request failure reported with exit status 1 by a command \
      operating on an existing session does not terminate that session. It \
      remains available for subsequent commands and does not need to be \
      restarted. This does not apply to protocol errors (exit status 123), \
      which may indicate that the server is unavailable. The $(b,stop) \
      command intentionally terminates the session.";
]

let _ =
  let cmds =
    [ init_cmd; stop_cmd; status_cmd; move_cmd; insert_cmd; delete_cmd;
      commit_cmd; goals_cmd ]
  in
  let default = Term.(ret (const (`Help(`Pager, None)))) in
  let default_info =
    let doc = "Command-line Rocq editor." in
    Cmd.info "rocq-ed" ~version ~exits ~doc ~man:main_man
  in
  exit (Cmd.eval (Cmd.group default_info ~default cmds))

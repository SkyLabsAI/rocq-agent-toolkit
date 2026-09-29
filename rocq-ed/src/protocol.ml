open Stdlib_extra.Extra

let cache_dir : Filepath.t Lazy.t = Lazy.from_fun @@ fun () ->
  let (/) = Filename.concat in
  match Sys.getenv_opt "XDG_CACHE_HOME" with
  | Some(dir) when dir <> "" -> dir / "rocq-ed"
  | _                        ->
  match Sys.getenv_opt "HOME" with
  | Some(dir) when dir <> "" -> dir / ".cache" / "rocq-ed"
  | _                        ->
  panic ~code:123 "Error: cannot locate the user's home directory."

type session_id = string

let get_data_dir : session_id -> Filepath.t = fun id ->
  let cache_dir = Lazy.force cache_dir in
  Filename.concat cache_dir id

let daemonize : ?log:Filepath.t -> (int -> unit) -> unit =
    fun ?(log="/dev/null") run ->
  (fun f -> Unix.handle_unix_error f ()) @@ fun () ->
  (* Detatch the process from the terminal. *)
  let pid = Unix.fork () in
  if pid > 0 then () else
  let _ = Unix.setsid () in
  let pid = Unix.fork () in
  if pid > 0 then exit 0;
  (* Change the stdout and stderr descriptors to write to the log. *)
  let log_fd = Unix.openfile log Unix.[O_WRONLY; O_CREAT; O_APPEND] 0o640 in
  Unix.dup2 log_fd Unix.stdout;
  Unix.dup2 log_fd Unix.stderr;
  Unix.close log_fd;
  (* Change the stdin descriptor to read from /dev/null. *)
  let null_fd = Unix.openfile "/dev/null" Unix.[O_RDONLY] 0 in
  Unix.dup2 null_fd Unix.stdin;
  Unix.close null_fd;
  (* get the PID of the daemon. *)
  let pid = Unix.handle_unix_error Unix.getpid () in
  run pid

let wait_for_file ~timeout ~interval file =
  try
    let t0 = Unix.gettimeofday () in
    let rec loop () =
      match Sys.file_exists file with true -> true | false ->
      let t1 = Unix.gettimeofday () in
      match t1 -. t0 >= timeout with true -> false | false ->
      Unix.sleepf interval; loop ()
    in
    loop ()
  with Unix.Unix_error(_,_,_) | Sys_error(_) -> false

let pid_file : string = "pid"

let init : Dune_util.config -> bool -> Filepath.t -> unit =
    fun config no_daemon rocq_file ->
  (* Handle exceptions. *)
  let handle f =
    try f () with
    | Sys_error(s) ->
        if not no_daemon then Printf.printf "false\n%!";
        panic ~code:123 "Error: system error (%s)." s
    | Unix.Unix_error(e,f,a) ->
        if not no_daemon then Printf.printf "false\n%!";
        let msg = Unix.error_message e in
        panic ~code:123 "Error: failed to \"%s %s\" (%s)." f a msg
    | e ->
        if not no_daemon then Printf.printf "false\n%!";
        raise e
  in
  handle @@ fun () ->
  assert (Sys.file_exists rocq_file);
  assert (Filename.extension rocq_file = ".v");
  (* Changing the working directory to the file's directory. *)
  let dir = Filename.dirname rocq_file in
  let basename = Filename.basename rocq_file in
  Sys.chdir dir;
  (* Get the CLI arguments and create create a document. *)
  match Dune_util.get_args config basename with
  | Error(s) ->
      if not no_daemon then Printf.printf "false\n%!";
      panic "Error: %s." s
  | Ok(args) ->
  match Document.init ~args ~file:basename with
  | exception Failure(s) ->
      if not no_daemon then Printf.printf "false\n%!";
      panic "Error: %s." s
  | d ->
  match Document.load_file d with
  | Error(s, _) ->
      if not no_daemon then Printf.printf "false\n%!";
      panic "Error: unable to load the file (%s)." s
  | Ok(())      ->
  (* Create the data directory. *)
  let cache_dir = Lazy.force cache_dir in
  Fileutil.mkdir ~mode:0o700 cache_dir;
  let data_dir = Filename.temp_dir ~temp_dir:cache_dir "" "" in
  let id = Filename.basename data_dir in
  (* Prepare the communication pipes. *)
  let req_fifo = Filename.concat data_dir "req.fifo" in
  Unix.mkfifo req_fifo 0o640;
  let res_fifo = Filename.concat data_dir "res.fifo" in
  Unix.mkfifo res_fifo 0o640;
  (* Prepare paths to other files in the data directory. *)
  let log_file = Filename.concat data_dir "log" in
  let pid_file = Filename.concat data_dir pid_file in
  (* Function running the server loop. *)
  let run pid =
    Fileutil.write_lines pid_file [Printf.sprintf "%i" pid];
    (* Logging function (will end up in the log file). *)
    let log fmt =
      let time = Unix.gettimeofday () in
      Format.printf ("%f: " ^^ fmt ^^ "\n%!") time
    in
    log "Started the process (pid %i)" pid;
    (* Single request handler. *)
    let handle_request () =
      log "Running request handler.";
      let req =
        In_channel.with_open_text req_fifo @@ fun ic ->
        log "Waiting for a request.";
        Marshal.from_channel ic
      in
      log "Request [%a] received." Request.pp req;
      let is_stop = Request.is_stop req in
      let res = Request.run d req in
      let _ =
        match res with
        | (_, Ok(_)) -> log "Request successful."
        | (_, Error(s, _)) ->
        match String.split_on_char '\n' (String.trim s) with
        | []     -> log "Request error."
        | [line] -> log "Request error [%s]." line
        | lines  ->
        log "Request error.";
        List.iter (Printf.printf "> %s\n%!") lines
      in
      if is_stop then Unix.unlink pid_file;
      let _ =
        Out_channel.with_open_text res_fifo @@ fun oc ->
        log "Sending response.";
        Marshal.to_channel oc res [];
        Out_channel.flush oc
      in
      log "Response sent.";
      not is_stop
    in
    (* Run the request loop. *)
    log "Running the request loop.";
    let rec loop () =
      let keep_going = handle_request () in
      if keep_going then loop ()
    in
    loop ();
    (* Cleanup and shutdown since a stop request must have been received. *)
    log "Exited the loop (stopping)."
  in
  match no_daemon with
  | true  ->
      Printf.printf "==== Environemnt for queries in the session ===\n%!";
      Printf.printf "ROCQED_SESSION_ID=%s\n%!" id;
      Printf.printf "===============================================\n%!";
      run (Unix.getpid ())
  | false ->
  daemonize ~log:log_file run;
  match wait_for_file ~timeout:2.0 ~interval:0.1 pid_file with
  | true  -> Printf.printf "export ROCQED_SESSION_ID=%s\n%!" id
  | false ->
  Printf.printf "false\n%!";
  panic ~code:123 "Error: the daemon never write its PID."

let full_client_request : type a b c. session_id -> (a, b, c) Request.t ->
    a * (b, string * c) Result.t = fun id req ->
  let data_dir = get_data_dir id in
  if not (Sys.file_exists data_dir) then
    panic ~code:123 "Error: No active session with ID %s." id;
  (* Attempt to take the client lock. *)
  let lock_dir = Filename.concat data_dir "client.lock" in
  let _ =
    try Sys.mkdir lock_dir 0o755 with Sys_error(s) ->
    if String.ends_with ~suffix:"File exists" s then
      panic ~code:123 "Error: a request is already in progress.";
    panic ~code:123 "Error: %s." s
  in
  (* Check that the server is running: opening the request FIFO without
     blocking fails with ENXIO when no process reads it. The server's PID is
     only meaningful in its own PID namespace, clients may be in another. The
     retry covers the server re-opening the FIFO after its last response. The
     request must be sent on this descriptor: the server fails on EOF. *)
  let req_fifo = Filename.concat data_dir "req.fifo" in
  let res_fifo = Filename.concat data_dir "res.fifo" in
  let deadline = Unix.gettimeofday () +. 1.0 in
  let rec open_req_fifo () =
    match Unix.openfile req_fifo Unix.[O_WRONLY; O_NONBLOCK; O_CLOEXEC] 0 with
    | fd -> Unix.clear_nonblock fd; fd
    | exception Unix.Unix_error(ENXIO, _, _)
        when Unix.gettimeofday () < deadline ->
        Unix.sleepf 0.05; open_req_fifo ()
    | exception Unix.Unix_error((ENXIO | ENOENT), _, _) ->
        Unix.rmdir lock_dir;
        panic ~code:123 "Error: Session with ID %s is stale or not ready." id
  in
  (* Run the request. *)
  let oc = Unix.out_channel_of_descr (open_req_fifo ()) in
  Marshal.to_channel oc req [];
  close_out oc;
  let res = In_channel.with_open_text res_fifo Marshal.from_channel in
  (* Release the lock, and return the response. *)
  Unix.rmdir lock_dir; res

let client_request : type a b. session_id -> (unit, a, b) Request.t ->
    (a, string * b) Result.t = fun rocq_file req ->
  snd (full_client_request rocq_file req)

let stop : session_id -> unit = fun id ->
  ignore (client_request id Request.Stop);
  let data_dir = get_data_dir id in
  let warn_unix_failure f x =
    try f x with Unix.Unix_error(e, f, args) ->
    let msg = Unix.error_message e in
    wrn "Warning: failed to \"%s %s\" (%s)." f args msg
  in
  let unlink file = warn_unix_failure Unix.unlink file in
  unlink (Filename.concat data_dir "req.fifo");
  unlink (Filename.concat data_dir "res.fifo");
  let log_file = Filename.concat data_dir "log" in
  if Sys.file_exists log_file then unlink log_file;
  warn_unix_failure Unix.rmdir data_dir

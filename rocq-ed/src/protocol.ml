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

(* Used to keep Unix-domain socket addresses short. *)
let in_dir : Filepath.t -> (unit -> 'a) -> 'a = fun dir f ->
  let cwd = Sys.getcwd () in
  Fun.protect ~finally:(fun () -> Sys.chdir cwd) @@ fun () ->
  Sys.chdir dir; f ()

let with_socket_channels socket_fd f =
  let output_fd =
    try Unix.dup ~cloexec:true socket_fd with
    | e -> Unix.close socket_fd; raise e
  in
  let ic = Unix.in_channel_of_descr socket_fd in
  let oc = Unix.out_channel_of_descr output_fd in
  let finally _ = close_out_noerr oc; close_in_noerr ic in
  Fun.protect ~finally (fun () -> f ic oc)

let pid_file : string = "pid"
let server_lock_file : string = "server.lock"
let client_lock_file : string = "client.lock"
let socket_file : string = "socket"

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
  (* Prepare paths to files in the data directory. *)
  let log_file = Filename.concat data_dir "log" in
  let pid_file = Filename.concat data_dir pid_file in
  let server_lock_file = Filename.concat data_dir server_lock_file in
  let client_lock_file = Filename.concat data_dir client_lock_file in
  (* Function running the server loop. *)
  let run ?(ready = fun () -> ()) pid =
    let lock_fd =
      Unix.openfile server_lock_file Unix.[O_WRONLY; O_CREAT] 0o640
    in
    Fun.protect ~finally:(fun () -> Unix.close lock_fd) @@ fun () ->
    Unix.lockf lock_fd F_LOCK 0;
    let client_lock_fd =
      Unix.openfile client_lock_file Unix.[O_WRONLY; O_CREAT] 0o640
    in
    Unix.close client_lock_fd;
    let socket_fd = Unix.socket ~cloexec:true PF_UNIX SOCK_STREAM 0 in
    Fun.protect ~finally:(fun () -> Unix.close socket_fd) @@ fun () ->
    in_dir data_dir (fun () -> Unix.bind socket_fd (ADDR_UNIX socket_file));
    Unix.listen socket_fd 1;
    Fileutil.write_lines pid_file [Printf.sprintf "%i" pid];
    ready ();
    (* Logging function (will end up in the log file). *)
    let log fmt =
      let time = Unix.gettimeofday () in
      Format.printf ("%f: " ^^ fmt ^^ "\n%!") time
    in
    log "Started the process (pid %i)" pid;
    (* Single request handler. *)
    let handle_request () =
      log "Running request handler.";
      log "Waiting for a request.";
      let (client_fd, _) = Unix.accept ~cloexec:true socket_fd in
      with_socket_channels client_fd @@ fun ic oc ->
      let req = Marshal.from_channel ic in
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
      log "Sending response.";
      Marshal.to_channel oc res [];
      Out_channel.flush oc;
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
      let ready () =
        Printf.printf "==== Environemnt for queries in the session ===\n%!";
        Printf.printf "ROCQED_SESSION_ID=%s\n%!" id;
        Printf.printf "===============================================\n%!"
      in
      run ~ready (Unix.getpid ())
  | false ->
  daemonize ~log:log_file (fun pid -> run pid);
  match wait_for_file ~timeout:2.0 ~interval:0.1 pid_file with
  | true  -> Printf.printf "export ROCQED_SESSION_ID=%s\n%!" id
  | false ->
  Printf.printf "false\n%!";
  panic ~code:123 "Error: the daemon never wrote its PID."

let full_client_request : type a b c. session_id -> (a, b, c) Request.t ->
    a * (b, string * c) Result.t = fun id req ->
  let data_dir = get_data_dir id in
  (* Check that the server is running. *)
  let pid_file = Filename.concat data_dir pid_file in
  match Sys.file_exists pid_file with
  | false -> panic ~code:123 "Error: No active session with ID %s." id
  | true  ->
  let server_lock_file = Filename.concat data_dir server_lock_file in
  let server_live =
    try
      let lock_fd = Unix.openfile server_lock_file Unix.[O_WRONLY] 0 in
      Fun.protect ~finally:(fun () -> Unix.close lock_fd) @@ fun () ->
      try Unix.lockf lock_fd F_TEST 0; false with
      | Unix.Unix_error((EACCES | EAGAIN), _, _) -> true
    with
    | Unix.Unix_error(ENOENT, _, _) ->
        panic ~code:123 "Error: Session with ID %s is stopping (or stale)." id
    | Unix.Unix_error(e, f, args)   ->
        let msg = Unix.error_message e in
        panic ~code:125 "Error: failed to \"%s %s\" (%s)." f args msg
  in
  match server_live with
  | false ->
      panic ~code:123 "Error: Session with ID %s crashed or was killed." id
  | true  ->
  (* Attempt to take the client lock. *)
  let client_lock_file = Filename.concat data_dir client_lock_file in
  let client_lock_fd =
    let fd = Unix.openfile client_lock_file Unix.[O_WRONLY] 0 in
    match Unix.lockf fd F_TLOCK 0 with
    | () -> fd
    | exception Unix.Unix_error((EACCES | EAGAIN), _, _) ->
        Unix.close fd;
        panic ~code:123 "Error: a request is already in progress."
    | exception e -> Unix.close fd; raise e
  in
  Fun.protect ~finally:(fun () -> Unix.close client_lock_fd) @@ fun () ->
  (* Connect to the server and run the request. *)
  let socket_fd =
    let fd = Unix.socket ~cloexec:true PF_UNIX SOCK_STREAM 0 in
    try
      in_dir data_dir @@ fun () ->
      Unix.connect fd (ADDR_UNIX socket_file); fd
    with e -> Unix.close fd; raise e
  in
  with_socket_channels socket_fd @@ fun ic oc ->
  Marshal.to_channel oc req [];
  Out_channel.flush oc;
  Marshal.from_channel ic

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
  unlink (Filename.concat data_dir socket_file);
  unlink (Filename.concat data_dir client_lock_file);
  unlink (Filename.concat data_dir server_lock_file);
  let log_file = Filename.concat data_dir "log" in
  if Sys.file_exists log_file then unlink log_file;
  warn_unix_failure Unix.rmdir data_dir

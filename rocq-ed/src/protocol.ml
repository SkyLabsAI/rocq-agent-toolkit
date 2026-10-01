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

type daemon_status =
  | Ready
  | Failed of int * string

(* Sandboxes may forbid Unix-domain sockets, which we rely on. *)
let unix_error_message : Unix.error -> string -> string -> string =
    fun e f a ->
  let msg = Unix.error_message e in
  let hint =
    match (e, f) with
    | (EPERM, ("bind" | "connect")) ->
        "\nHint: the environment (e.g., a sandbox without network access) \
         probably forbids Unix-domain sockets, which rocq-ed relies on."
    | _ -> ""
  in
  Printf.sprintf "Error: failed to \"%s %s\" (%s).%s" f a msg hint

let error_of_exception = function
  | Sys_error(s) ->
      (123, Printf.sprintf "Error: system error (%s)." s)
  | Unix.Unix_error(e, f, a) ->
      (123, unix_error_message e f a)
  | e ->
      let msg = Printexc.to_string e in
      (125, Printf.sprintf "Error: daemon failed unexpectedly (%s)." msg)

let daemonize : ?log:Filepath.t ->
    (notify:(daemon_status -> unit) -> int -> unit) -> daemon_status =
    fun ?(log="/dev/null") run ->
  (* Pipe used for the deamon to notify the original process of its status. *)
  let (status_in, status_out) = Unix.pipe ~cloexec:true () in
  (* Fork and have the parent wait for the status on the pipe. *)
  match Unix.fork () with
  | exception e -> Unix.close status_in; Unix.close status_out; raise e
  | pid when pid <> 0 ->
      Unix.close status_out;
      (* Wait for the intermediate child (used by the double fork). *)
      let rec wait () =
        try ignore (Unix.waitpid [] pid) with Unix.Unix_error(EINTR, _, _) ->
        wait ()
      in
      wait ();
      (* Wait for the daemon to report its status. *)
      let ic = Unix.in_channel_of_descr status_in in
      Fun.protect ~finally:(fun () -> close_in_noerr ic) @@ fun () ->
      begin
        try (Marshal.from_channel ic : daemon_status) with
        | End_of_file ->
            Failed(125, "Error: the daemon exited during startup.")
        | Failure(s) ->
            Failed(125, "Error: failed to read daemon status (" ^ s ^ ").")
      end
  | _ ->
  Unix.close status_in;
  let oc = Unix.out_channel_of_descr status_out in
  let notified = ref false in
  let exit_code = ref 0 in
  let notify status =
    match !notified with true -> () | false ->
    notified := true;
    (match status with Failed(code, _) -> exit_code := code | _ -> ());
    Fun.protect ~finally:(fun () -> close_out_noerr oc) @@ fun () ->
    Marshal.to_channel oc status [];
    Out_channel.flush oc
  in
  let redirected = ref false in
  let fail e =
    let (code, msg) = error_of_exception e in
    notify (Failed(code, msg));
    if !redirected then Format.eprintf "%s\n%!" msg;
    Unix._exit code
  in
  try
    ignore (Unix.setsid ());
    match Unix.fork () with
    | pid when pid <> 0 -> close_out_noerr oc; Unix._exit 0
    | _ ->
    (* Change stdout and stderr to write to the session log. *)
    let log_fd =
      Unix.openfile log Unix.[O_WRONLY; O_CREAT; O_APPEND] 0o640
    in
    Unix.dup2 log_fd Unix.stdout;
    Unix.dup2 log_fd Unix.stderr;
    Unix.close log_fd;
    (* Change stdin to read from /dev/null. *)
    let null_fd = Unix.openfile "/dev/null" Unix.[O_RDONLY] 0 in
    Unix.dup2 null_fd Unix.stdin;
    Unix.close null_fd;
    redirected := true;
    run ~notify (Unix.getpid ());
    if not !notified then begin
      let msg = "Error: the daemon did not report readiness." in
      notify (Failed(125, msg))
    end;
    Unix._exit !exit_code
  with e -> fail e

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
        panic ~code:123 "%s" (unix_error_message e f a)
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
  (* Get the CLI arguments. *)
  match Dune_util.get_args config basename with
  | Error(s) ->
      if not no_daemon then Printf.printf "false\n%!";
      panic "Error: %s." s
  | Ok(args) ->
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
  let socket_path = Filename.concat data_dir socket_file in
  (* Remove (partial) data directory. *)
  let cleanup_data_dir () =
    let remove file = try Sys.remove file with Sys_error(_) -> () in
    List.iter remove
      [socket_path; pid_file; client_lock_file; server_lock_file; log_file];
    try Sys.rmdir data_dir with Sys_error(_) -> ()
  in
  (* Document initialization holds on to stderr: run after daemonizing. *)
  let init_document () =
    match Document.init ~args ~file:basename with
    | exception Failure(s) -> Error(1, Printf.sprintf "Error: %s." s)
    | d ->
    let stop () = try Document.stop d with _ -> () in
    match Document.load_file d with
    | exception e -> stop (); raise e
    | Ok(()) -> Ok(d)
    | Error(s, _) ->
    stop ();
    Error(1, Printf.sprintf "Error: unable to load the file (%s)." s)
  in
  (* Function running the server loop. *)
  let run d ?(ready = fun () -> ()) pid =
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
      begin
        (* The client may have gone away: drop the response. *)
        try
          Marshal.to_channel oc res [];
          Out_channel.flush oc;
          log "Response sent."
        with Sys_error(s) -> log "Failed to send the response (%s)." s
      end;
      not is_stop
    in
    (* Writing to the socket of a client that went away must not kill us. *)
    Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
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
  let run_daemon () =
    let status =
      try
        daemonize ~log:log_file @@ fun ~notify pid ->
        match init_document () with
        | Error(code, msg) -> notify (Failed(code, msg))
        | Ok(d)            ->
        Fun.protect ~finally:(fun () -> Document.stop d) @@ fun () ->
        run d ~ready:(fun () -> notify Ready) pid
      with e ->
        cleanup_data_dir ();
        raise e
    in
    match status with
    | Ready -> Printf.printf "export ROCQED_SESSION_ID=%s\n%!" id
    | Failed(code, s) ->
        cleanup_data_dir (); Printf.printf "false\n%!"; panic ~code "%s" s
  in
  let run_no_daemon () =
    match init_document () with
    | exception e -> cleanup_data_dir (); raise e
    | Error(code, s) -> cleanup_data_dir (); panic ~code "%s" s
    | Ok(d) ->
    let ready () =
      Printf.printf "==== Environemnt for queries in the session ===\n%!";
      Printf.printf "ROCQED_SESSION_ID=%s\n%!" id;
      Printf.printf "===============================================\n%!"
    in
    Fun.protect ~finally:(fun () -> Document.stop d) @@ fun () ->
    run d ~ready (Unix.getpid ())
  in
  if no_daemon then run_no_daemon () else run_daemon ()

(* Check that the session exists, and return [false] if its server crashed or
   was killed. *)
let server_live : session_id -> bool = fun id ->
  let data_dir = get_data_dir id in
  let pid_file = Filename.concat data_dir pid_file in
  match Sys.file_exists pid_file with
  | false -> panic ~code:123 "Error: No active session with ID %s." id
  | true  ->
  let server_lock_file = Filename.concat data_dir server_lock_file in
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

let full_client_request : type a b c. session_id -> (a, b, c) Request.t ->
    a * (b, string * c) Result.t = fun id req ->
  let data_dir = get_data_dir id in
  (* Check that the server is running. *)
  match server_live id with
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
    with
    | Unix.Unix_error(EPERM, f, a) ->
        Unix.close fd; panic ~code:123 "%s" (unix_error_message EPERM f a)
    | e -> Unix.close fd; raise e
  in
  with_socket_channels socket_fd @@ fun ic oc ->
  Marshal.to_channel oc req [];
  Out_channel.flush oc;
  Marshal.from_channel ic

let client_request : type a b. session_id -> (unit, a, b) Request.t ->
    (a, string * b) Result.t = fun rocq_file req ->
  snd (full_client_request rocq_file req)

let stop : session_id -> unit = fun id ->
  (* The data directory of a dead session is cleaned up as well. *)
  let live = server_live id in
  if live then ignore (client_request id Request.Stop)
  else wrn "Warning: Session with ID %s crashed or was killed." id;
  let data_dir = get_data_dir id in
  let warn_unix_failure f x =
    try f x with Unix.Unix_error(e, f, args) ->
    let msg = Unix.error_message e in
    wrn "Warning: failed to \"%s %s\" (%s)." f args msg
  in
  let unlink file = warn_unix_failure Unix.unlink file in
  if not live then unlink (Filename.concat data_dir pid_file);
  unlink (Filename.concat data_dir socket_file);
  unlink (Filename.concat data_dir client_lock_file);
  unlink (Filename.concat data_dir server_lock_file);
  let log_file = Filename.concat data_dir "log" in
  if Sys.file_exists log_file then unlink log_file;
  warn_unix_failure Unix.rmdir data_dir

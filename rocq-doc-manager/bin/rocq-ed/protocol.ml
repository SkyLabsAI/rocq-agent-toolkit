open Stdlib_extra.Extra
open Panic

let daemonize : ?log:Filepath.t -> unit -> int = fun ?(log="/dev/null") _ ->
  (fun f -> Unix.handle_unix_error f ()) @@ fun _ ->
  (* Detatch the process from the terminal. *)
  let pid = Unix.fork () in
  if pid > 0 then exit 0;
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
  (* Return the PID of the daemon. *)
  Unix.handle_unix_error Unix.getpid ()

let daemon_pid_file : string = "daemon.pid"
let data_dir_suffix : string = ".rocqed" (* no dash to not confuse dune *)

let data_dir_of_basename : string -> string = fun basename ->
  "." ^ basename ^ data_dir_suffix

let is_pid_running : int -> bool = fun pid ->
  try Unix.kill pid 0; true
  with Unix.Unix_error(ESRCH, _, _) -> false

let is_session_active : data_dir:string -> bool = fun ~data_dir ->
  let pid_file = Filename.concat data_dir daemon_pid_file in
  match Fileutil.read_lines pid_file with
  | [pid] -> is_pid_running (int_of_string pid)
  | exception _ | _ -> false

let clean_data_dir : data_dir:string -> unit = fun ~data_dir ->
  let files_in_dir dir =
    List.map (Filename.concat dir) @@ Array.to_list @@ Sys.readdir dir
  in
  let rec go files =
    match files with
    | dir :: files when Sys.is_directory dir ->
      let new_files = files_in_dir dir in
      go @@ new_files @ files;
      Unix.rmdir dir
    | file :: files ->
      if Sys.file_exists file then begin
        Unix.unlink file
      end;
      go files
    | [] -> ()
  in
  go @@ files_in_dir data_dir


let init : Dune_util.config -> Filepath.t -> unit = fun config rocq_file ->
  assert (Sys.file_exists rocq_file);
  assert (Filename.extension rocq_file = ".v");
  (* Changing the working directory to the file's directory. *)
  let dir = Filename.dirname rocq_file in
  let rocq_file = Filename.basename rocq_file in
  Sys.chdir dir;
  (* Create the data directory, which also locks the session for the file. *)
  let data_dir = data_dir_of_basename rocq_file in
  begin try Sys.mkdir data_dir 0o755 with Sys_error(s) ->
    if String.ends_with ~suffix:"File exists" s then begin
      if is_session_active ~data_dir then
        panic "Error: a session is already running for that file."
      else begin
        wrn "Warning: Clearning up stale directory %s" data_dir;
        clean_data_dir ~data_dir
      end
    end else begin
      panic "Error: %s." s
    end
  end;
  (* Get the CLI arguments and create create a document. *)
  let args = Dune_util.get_args config rocq_file in
  let d = Document.init ~args ~file:rocq_file in
  match Document.load_file d with
  | Error(s, _) -> panic "Error: unable to load the file (%s)." s
  | Ok(())      ->
  (* Prepare the communication pipes. *)
  let req_fifo = Filename.concat data_dir "req.fifo" in
  Unix.mkfifo req_fifo 0o640;
  let res_fifo = Filename.concat data_dir "res.fifo" in
  Unix.mkfifo res_fifo 0o640;
  (* Daemonize the process, and write its PID to a file. *)
  let log_file = Filename.concat data_dir "log" in
  let pid = daemonize ~log:log_file () in
  let pid_file = Filename.concat data_dir daemon_pid_file in
  Fileutil.write_lines pid_file [Printf.sprintf "%i" pid];
  (* Logging function (will end up in the log file). *)
  let log fmt =
    let time = Unix.gettimeofday () in
    Format.printf ("%f: " ^^ fmt ^^ "\n%!") time
  in
  log "Started the daemon (pid %i)" pid;
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
      | Ok(_) -> log "Request successful."
      | Error(s, _) ->
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
  log "Reached deamon shutdown.";
  exit 0

let client_request : type a b. Filepath.t -> (a, b) Request.t ->
    (a, string * b) Result.t = fun rocq_file req ->
  assert (Sys.file_exists rocq_file);
  assert (Filename.extension rocq_file = ".v");
  (* Check that the daemon is running. *)
  let data_dir = data_dir_of_basename rocq_file in
  let pid_file = Filename.concat data_dir daemon_pid_file in
  if not (Sys.file_exists data_dir) then
    panic "Error: no active session for %S." rocq_file;
  if not (Sys.file_exists pid_file) then
    panic "Error: session daemon is not ready for %S." rocq_file;
  (* Attempt to take the client lock. *)
  let lock_dir = Filename.concat data_dir "client.lock" in
  let _ =
    try Sys.mkdir lock_dir 0o755 with Sys_error(s) ->
    if String.ends_with ~suffix:"File exists" s then
      panic "Error: a request is already in progress.";
    panic "Error: %s." s
  in
  (* Run the request. *)
  let req_fifo = Filename.concat data_dir "req.fifo" in
  let res_fifo = Filename.concat data_dir "res.fifo" in
  let _ =
    Out_channel.with_open_text req_fifo @@ fun oc ->
    Marshal.to_channel oc req [];
    Out_channel.flush oc
  in
  let res = In_channel.with_open_text res_fifo Marshal.from_channel in
  (* Release the lock, and return the response. *)
  Unix.rmdir lock_dir; res

let stop : Filepath.t -> unit = fun rocq_file ->
  let data_dir = data_dir_of_basename rocq_file in
    if not @@ is_session_active ~data_dir && Sys.file_exists data_dir then begin
      wrn "Warning: No session active. Clearning up stale directory %s" data_dir;
      clean_data_dir ~data_dir;
      Unix.rmdir data_dir
    end
    else begin
      ignore (client_request rocq_file Request.Stop);
      let req_fifo = Filename.concat data_dir "req.fifo" in
      let res_fifo = Filename.concat data_dir "res.fifo" in
      List.iter Unix.unlink [req_fifo; res_fifo];
      let log_file = Filename.concat data_dir "log" in
      if Sys.file_exists log_file then Unix.unlink log_file;
      Unix.rmdir data_dir
    end


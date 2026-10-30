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

let error_of_exception = function
  | Sys_error(s) ->
      (123, Printf.sprintf "Error: system error (%s)." s)
  | Unix.Unix_error(e, f, a) ->
      let msg = Unix.error_message e in
      (123, Printf.sprintf "Error: failed to \"%s %s\" (%s)." f a msg)
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
  Fun.protect ~finally (fun () -> f socket_fd ic oc)

let pid_file : string = "pid"
let server_lock_file : string = "server.lock"
let client_lock_file : string = "client.lock"
let socket_file : string = "socket"
let interrupt_socket_file : string = "interrupt.socket"

type request_state = Running | Cancelled | Publishing | Finished

type interrupt_mode = Cooperative | Hard

type interrupt_result =
  | Interrupt_requested
  | No_active_request
  | No_active_operation

type active_request = {
  document : Document.t;
  state : request_state Atomic.t;
  control_mutex : Mutex.t;
  hard_killed : bool Atomic.t;
}

type request_watcher = {
  thread : Thread.t;
  wake_fd : Unix.file_descr;
  escalated : bool Atomic.t;
}

let interrupt_grace_period = 0.5
let interrupt_poll_period = 0.01

let close_noerr fd =
  try Unix.close fd with Unix.Unix_error(_) -> ()

let select_read fds timeout =
  try
    let (readable, _, _) = Unix.select fds [] [] timeout in
    readable
  with Unix.Unix_error(EINTR, _, _) ->
    []

let consume_byte fd =
  let byte = Bytes.create 1 in
  try ignore (Unix.read fd byte 0 1) with
  | Unix.Unix_error(_) -> ()

let start_request_watcher ~log client_fd state document =
  let (wake_in, wake_out) = Unix.pipe ~cloexec:true () in
  let escalated = Atomic.make false in
  let watch () =
    Fun.protect ~finally:(fun () -> close_noerr wake_in) @@ fun () ->
    let byte = Bytes.create 1 in
    let rec wait_for_disconnect () =
      let readable = select_read [client_fd; wake_in] (-1.) in
      if List.mem wake_in readable then
        consume_byte wake_in
      else if List.mem client_fd readable then begin
        match Unix.read client_fd byte 0 1 with
        | 0 -> cancel_request ()
        | _ -> wait_for_disconnect ()
        | exception Unix.Unix_error(EINTR, _, _) ->
            wait_for_disconnect ()
        | exception Unix.Unix_error(error, fn, arg) ->
            let message = Unix.error_message error in
            log (Printf.sprintf
              "Client socket failed during request [%s %s: %s]."
              fn arg message);
            cancel_request ()
      end else
        wait_for_disconnect ()
    (* A request may start a top-level operation after its disconnect is
       observed. Keep retrying until it finishes, switching to a hard
       interruption after the grace period. *)
    and cancel_request () =
      if Atomic.compare_and_set state Running Cancelled then begin
        log "Client disconnected; requesting cooperative interruption.";
        request_cooperative_interrupt (Mtime_clock.counter ())
      end
    and wait_then delay f =
      let readable = select_read [wake_in] delay in
      if List.mem wake_in readable then consume_byte wake_in else f ()
    and request_cooperative_interrupt counter =
      if Atomic.get state <> Cancelled then () else begin
        begin try ignore (Document.interrupt document) with e ->
          log (Printf.sprintf "Failed to request interruption [%s]."
            (Printexc.to_string e))
        end;
        let elapsed = Mtime_clock.count counter in
        let elapsed = Mtime.Span.to_float_ns elapsed /. 1e9 in
        let remaining = interrupt_grace_period -. elapsed in
        if remaining <= 0. then
          request_hard_interrupt ()
        else
          wait_then (min interrupt_poll_period remaining)
            (fun () -> request_cooperative_interrupt counter)
      end
    and request_hard_interrupt () =
      if Atomic.get state <> Cancelled then () else
      match Document.kill document with
      | true ->
          Atomic.set escalated true;
          log "Interruption timed out; killed the Rocq top-level."
      | false ->
          wait_then interrupt_poll_period request_hard_interrupt
      | exception e ->
          log (Printf.sprintf "Failed to kill the Rocq top-level [%s]."
            (Printexc.to_string e));
          wait_then interrupt_poll_period request_hard_interrupt
    in
    wait_for_disconnect ()
  in
  let thread =
    try Thread.create (fun () ->
      try watch () with e ->
        log (Printf.sprintf "Request watcher failed [%s]."
          (Printexc.to_string e))
    ) () with e ->
      close_noerr wake_in;
      close_noerr wake_out;
      raise e
  in
  {thread; wake_fd = wake_out; escalated}

let finish_request_watcher watcher =
  let byte = Bytes.make 1 '\000' in
  begin try ignore (Unix.single_write watcher.wake_fd byte 0 1) with
  | Unix.Unix_error(_) -> ()
  end;
  close_noerr watcher.wake_fd;
  Thread.join watcher.thread

type interrupt_server = {
  thread : Thread.t;
  wake_fd : Unix.file_descr;
}

let current_request active request =
  match Atomic.get active with
  | Some(current) -> current == request
  | None -> false

let handle_interrupt active mode =
  match Atomic.get active with
  | None -> No_active_request
  | Some(request) ->
  Mutex.protect request.control_mutex @@ fun () ->
  if not (current_request active request) ||
      Atomic.get request.state <> Running then
    No_active_request
  else
    let requested =
      match mode with
      | Cooperative -> Document.interrupt request.document
      | Hard ->
          let requested = Document.kill request.document in
          if requested then Atomic.set request.hard_killed true;
          requested
    in
    if requested then Interrupt_requested else No_active_operation

let start_interrupt_server ~log socket_fd active =
  let (wake_in, wake_out) = Unix.pipe ~cloexec:true () in
  let send_response oc response =
    try
      Marshal.to_channel oc response [];
      Out_channel.flush oc
    with
    | (Sys_error(_) | Unix.Unix_error(_)) as e ->
        log (Printf.sprintf "Interrupt response failed [%s]."
          (Printexc.to_string e))
  in
  let handle_client client_fd =
    with_socket_channels client_fd @@ fun _ ic oc ->
    let mode =
      try Some((Marshal.from_channel ic : interrupt_mode)) with
      | End_of_file ->
          log "Interrupt client disconnected while sending its request.";
          None
      | Failure(message) | Invalid_argument(message) ->
          log (Printf.sprintf "Malformed interrupt request [%s]." message);
          None
      | (Sys_error(_) | Unix.Unix_error(_)) as e ->
          log (Printf.sprintf "Interrupt request failed [%s]."
            (Printexc.to_string e));
          None
    in
    Option.iter (fun mode ->
      let response = handle_interrupt active mode in
      begin match (mode, response) with
      | (Cooperative, Interrupt_requested) ->
          log "Explicit cooperative interruption requested."
      | (Hard, Interrupt_requested) ->
          log "Explicit hard interruption requested."
      | (_, No_active_request) ->
          log "Explicit interruption found no active request."
      | (_, No_active_operation) ->
          log "Explicit interruption found no active Rocq operation."
      end;
      send_response oc response
    ) mode
  in
  let rec loop () =
    let readable = select_read [socket_fd; wake_in] (-1.) in
    if List.mem wake_in readable then
      consume_byte wake_in
    else if List.mem socket_fd readable then begin
      begin match Unix.accept ~cloexec:true socket_fd with
      | (client_fd, _) ->
          begin try handle_client client_fd with e ->
            log (Printf.sprintf "Interrupt handler failed [%s]."
              (Printexc.to_string e))
          end
      | exception Unix.Unix_error(EINTR, _, _) -> ()
      | exception e -> raise e
      end;
      loop ()
    end else
      loop ()
  in
  let thread =
    try Thread.create (fun () ->
      Fun.protect ~finally:(fun () -> close_noerr wake_in) @@ fun () ->
      try loop () with e ->
        log (Printf.sprintf "Interrupt server failed [%s]."
          (Printexc.to_string e))
    ) () with e ->
      close_noerr wake_in;
      close_noerr wake_out;
      raise e
  in
  {thread; wake_fd = wake_out}

let finish_interrupt_server server =
  let byte = Bytes.make 1 '\000' in
  begin try ignore (Unix.single_write server.wake_fd byte 0 1) with
  | Unix.Unix_error(_) -> ()
  end;
  close_noerr server.wake_fd;
  Thread.join server.thread

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
  let interrupt_socket_path =
    Filename.concat data_dir interrupt_socket_file
  in
  (* Remove (partial) data directory. *)
  let cleanup_data_dir () =
    let remove file = try Sys.remove file with Sys_error(_) -> () in
    List.iter remove
      [socket_path; interrupt_socket_path; pid_file; client_lock_file;
       server_lock_file; log_file];
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
    let interrupt_socket_fd =
      Unix.socket ~cloexec:true PF_UNIX SOCK_STREAM 0
    in
    Fun.protect
      ~finally:(fun () -> Unix.close interrupt_socket_fd) @@ fun () ->
    in_dir data_dir (fun () ->
      Unix.bind socket_fd (ADDR_UNIX socket_file);
      Unix.bind interrupt_socket_fd (ADDR_UNIX interrupt_socket_file));
    Unix.listen socket_fd 1;
    Unix.listen interrupt_socket_fd 1;
    Fileutil.write_lines pid_file [Printf.sprintf "%i" pid];
    Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
    (* Logging function (will end up in the log file). *)
    let log_mutex = Mutex.create () in
    let log fmt =
      Format.kasprintf (fun message ->
        Mutex.protect log_mutex @@ fun () ->
        let time = Unix.gettimeofday () in
        Format.printf "%f: %s\n%!" time message
      ) fmt
    in
    let log_message message = log "%s" message in
    log "Started the process (pid %i)" pid;
    let active_request = Atomic.make None in
    let interrupt_server =
      start_interrupt_server ~log:log_message interrupt_socket_fd
        active_request
    in
    Fun.protect
      ~finally:(fun () -> finish_interrupt_server interrupt_server) @@
      fun () ->
    ready ();
    let restart_backend () =
      log "Restarting the Rocq backend.";
      try
        Document.restart d;
        log "Rocq backend restarted."
      with e ->
        log "Failed to restart the Rocq backend [%s]."
          (Printexc.to_string e);
        raise e
    in
    let send_response oc response =
      log "Sending response.";
      try
        Marshal.to_channel oc response [];
        Out_channel.flush oc;
        log "Response sent."
      with
      | (Sys_error(_) | Unix.Unix_error(_)) as e ->
          log "Response could not be delivered [%s]."
            (Printexc.to_string e)
    in
    let log_response response =
      match response with
      | (_, Ok(_)) -> log "Request successful."
      | (_, Error(s, _)) ->
      match String.split_on_char '\n' (String.trim s) with
      | []     -> log "Request error."
      | [line] -> log "Request error [%s]." line
      | lines  ->
      log "Request error.";
      List.iter (fun line -> log "> %s" line) lines
    in
    let run_request : type a b c.
        Unix.file_descr -> out_channel -> (a, b, c) Request.t -> bool =
        fun client_fd oc req ->
      log "Request [%a] received." Request.pp req;
      let is_stop = Request.is_stop req in
      let working = Document.clone d in
      let state = Atomic.make Running in
      let watcher =
        try start_request_watcher ~log:log_message client_fd state working
        with e ->
          Document.stop working;
          raise e
      in
      let request = {
        document = working;
        state;
        control_mutex = Mutex.create ();
        hard_killed = Atomic.make false;
      }
      in
      Atomic.set active_request (Some(request));
      let active_cleared = ref false in
      let watcher_finished = ref false in
      let working_stopped = ref false in
      let clear_active f =
        Mutex.protect request.control_mutex @@ fun () ->
        f ();
        if current_request active_request request then
          Atomic.set active_request None;
        active_cleared := true
      in
      let finish_watcher () =
        if not !watcher_finished then begin
          watcher_finished := true;
          finish_request_watcher watcher
        end
      in
      let stop_working () =
        if not !working_stopped then begin
          working_stopped := true;
          Document.stop working
        end
      in
      let backend_needs_restart () =
        Atomic.get watcher.escalated || Atomic.get request.hard_killed
      in
      let cleanup () =
        if not !active_cleared then
          clear_active (fun () -> Atomic.set state Finished)
        else
          Atomic.set state Finished;
        finish_watcher ();
        stop_working ()
      in
      Fun.protect ~finally:cleanup @@ fun () ->
      match Request.run working req with
      | response ->
          let publish = ref false in
          clear_active (fun () ->
            if Atomic.compare_and_set state Running Publishing then
              publish := true
            else begin
              assert (Atomic.get state = Cancelled);
              Atomic.set state Finished
            end);
          if !publish then begin
            finish_watcher ();
            Document.copy_contents ~from:working d;
            stop_working ();
            if backend_needs_restart () then restart_backend ();
            log_response response;
            if is_stop then Unix.unlink pid_file;
            Atomic.set state Finished;
            send_response oc response;
            not is_stop
          end else begin
            finish_watcher ();
            stop_working ();
            log "Discarding the result of a cancelled request.";
            if backend_needs_restart () then restart_backend ();
            true
          end
      | exception Document.Interrupted(Rocq_toplevel.Interrupt) ->
          clear_active (fun () -> Atomic.set state Finished);
          finish_watcher ();
          stop_working ();
          log "Cooperative interruption acknowledged.";
          if backend_needs_restart () then restart_backend ();
          true
      | exception Document.Interrupted(Rocq_toplevel.Killed) ->
          clear_active (fun () -> Atomic.set state Finished);
          finish_watcher ();
          stop_working ();
          log "Request interrupted by a hard kill.";
          restart_backend ();
          true
      | exception Document.Interrupted(Rocq_toplevel.Failed(error)) ->
          clear_active (fun () -> Atomic.set state Finished);
          finish_watcher ();
          stop_working ();
          log "Request failed because the Rocq backend failed [%s]."
            (Printexc.to_string error);
          restart_backend ();
          true
      | exception ((Out_of_memory | Stack_overflow) as e) ->
          raise e
      | exception e ->
          clear_active (fun () -> Atomic.set state Finished);
          finish_watcher ();
          stop_working ();
          log "Request failed unexpectedly [%s]." (Printexc.to_string e);
          if backend_needs_restart () then restart_backend ();
          true
    in
    let decode_request client_fd ic oc =
      let request =
        try Some(Marshal.from_channel ic) with
        | End_of_file ->
            log "Client disconnected while sending a request.";
            None
        | Failure(message) ->
            log "Malformed request [%s]." message;
            None
        | Invalid_argument(message) ->
            log "Invalid request [%s]." message;
            None
        | Sys_error(message) ->
            log "Request read failed [%s]." message;
            None
        | Unix.Unix_error(error, fn, arg) ->
            let message = Unix.error_message error in
            log "Request read failed [%s %s: %s]." fn arg message;
            None
      in
      match request with
      | None      -> true
      | Some(req) -> run_request client_fd oc req
    in
    let rec accept () =
      try Unix.accept ~cloexec:true socket_fd with
      | Unix.Unix_error(EINTR, _, _) -> accept ()
    in
    (* Single request handler. *)
    let handle_request () =
      log "Running request handler.";
      log "Waiting for a request.";
      let (client_fd, _) = accept () in
      with_socket_channels client_fd @@ fun client_fd ic oc ->
      decode_request client_fd ic oc
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
      Printf.printf "==== Environment for this rocq-ed session ====\n%!";
      Printf.printf "ROCQED_SESSION_ID=%s\n%!" id;
      Printf.printf "===============================================\n%!"
    in
    Fun.protect ~finally:(fun () -> Document.stop d) @@ fun () ->
    run d ~ready (Unix.getpid ())
  in
  if no_daemon then run_no_daemon () else run_daemon ()

let check_server_live id data_dir =
  let pid_file = Filename.concat data_dir pid_file in
  if not (Sys.file_exists pid_file) then
    panic ~code:123 "Error: no active session with ID %s." id;
  let server_lock_file = Filename.concat data_dir server_lock_file in
  let server_live =
    try
      let lock_fd = Unix.openfile server_lock_file Unix.[O_WRONLY] 0 in
      Fun.protect ~finally:(fun () -> Unix.close lock_fd) @@ fun () ->
      try Unix.lockf lock_fd F_TEST 0; false with
      | Unix.Unix_error((EACCES | EAGAIN), _, _) -> true
    with
    | Unix.Unix_error(ENOENT, _, _) ->
        panic ~code:123 "Error: session with ID %s is stopping (or stale)." id
    | Unix.Unix_error(e, f, args)   ->
        let msg = Unix.error_message e in
        panic ~code:125 "Error: failed to \"%s %s\" (%s)." f args msg
  in
  if not server_live then
    panic ~code:123 "Error: session with ID %s crashed or was killed." id

let interrupt : session_id -> kill:bool -> interrupt_result = fun id ~kill ->
  let data_dir = get_data_dir id in
  check_server_live id data_dir;
  let socket_fd =
    let fd = Unix.socket ~cloexec:true PF_UNIX SOCK_STREAM 0 in
    try
      in_dir data_dir @@ fun () ->
      Unix.connect fd (ADDR_UNIX interrupt_socket_file); fd
    with e -> Unix.close fd; raise e
  in
  try
    with_socket_channels socket_fd @@ fun _ ic oc ->
    Marshal.to_channel oc (if kill then Hard else Cooperative) [];
    Out_channel.flush oc;
    (Marshal.from_channel ic : interrupt_result)
  with
  | Unix.Unix_error(e, f, args) ->
      let msg = Unix.error_message e in
      panic ~code:125 "Error: failed to \"%s %s\" (%s)." f args msg
  | Sys_error(s) ->
      panic ~code:125 "Error: system error (%s)." s
  | End_of_file ->
      panic ~code:125 "Error: end of file when getting interrupt response."

let full_client_request : type a b c. session_id -> (a, b, c) Request.t ->
    a * (b, string * c) Result.t = fun id req ->
  let data_dir = get_data_dir id in
  check_server_live id data_dir;
  (* Attempt to take the client lock. *)
  let client_lock_file = Filename.concat data_dir client_lock_file in
  let client_lock_fd =
    let fd = Unix.openfile client_lock_file Unix.[O_WRONLY] 0 in
    match Unix.lockf fd F_TLOCK 0 with
    | () -> fd
    | exception Unix.Unix_error((EACCES | EAGAIN), _, _) ->
        Unix.close fd;
        panic ~code:75 "Error: a request is already in progress."
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
  try
    with_socket_channels socket_fd @@ fun _ ic oc ->
    Marshal.to_channel oc req [];
    Out_channel.flush oc;
    Marshal.from_channel ic
  with
  | Unix.Unix_error(e, f, args) ->
      let msg = Unix.error_message e in
      panic ~code:125 "Error: failed to \"%s %s\" (%s)." f args msg
  | Sys_error(s) ->
      panic ~code:125 "Error: system error (%s)." s
  | End_of_file ->
      panic ~code:125 "Error: end of file when getting server response."

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
  unlink (Filename.concat data_dir interrupt_socket_file);
  unlink (Filename.concat data_dir client_lock_file);
  unlink (Filename.concat data_dir server_lock_file);
  let log_file = Filename.concat data_dir "log" in
  if Sys.file_exists log_file then unlink log_file;
  warn_unix_failure Unix.rmdir data_dir

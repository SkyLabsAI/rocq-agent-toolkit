open Rocq_simple_api_internal.Rocq_toplevel_data

let loc = Loc.initial Loc.ToplevelInput

let failf fmt = Printf.ksprintf failwith fmt

let rec waitpid pid =
  try snd (Unix.waitpid [] pid) with
  | Unix.Unix_error(EINTR, _, _) -> waitpid pid

let close_fd_noerr fd =
  try Unix.close fd with Unix.Unix_error(_, _, _) -> ()

let touch path =
  let oc = open_out path in
  close_out oc

let rec wait_for_file path attempts =
  if Sys.file_exists path then () else if attempts = 0 then
    failf "timed out waiting for %s" path
  else begin
    Thread.delay 0.001;
    wait_for_file path (attempts - 1)
  end

let rec remove_tree path =
  if Sys.file_exists path then
    if Sys.is_directory path then begin
      Array.iter (fun name -> remove_tree (Filename.concat path name))
        (Sys.readdir path);
      Unix.rmdir path
    end else
      Unix.unlink path

let with_temp_dir prefix f =
  let dir = Filename.temp_dir prefix "" in
  Fun.protect ~finally:(fun () -> remove_tree dir) (fun () -> f dir)

let send oc value =
  Marshal.to_channel oc value [];
  Out_channel.flush oc

let fake_startup_failure () =
  touch (Sys.getenv "ROCQ_SIMPLE_API_TEST_PEER_MARKER");
  Thread.delay 0.3;
  exit 2

let fake_cancel_failure () =
  send stdout (Unix.getpid (), 1);
  let request =
    (Marshal.from_channel stdin : (unit, unit) request)
  in
  touch (Sys.getenv "ROCQ_SIMPLE_API_TEST_PEER_MARKER");
  wait_for_file (Sys.getenv "ROCQ_SIMPLE_API_TEST_PEER_GO") 5000;
  Unix.close (Unix.descr_of_in_channel stdin);
  send stdout (Started request.request_id : (unit, unit) message);
  while true do Thread.delay 1. done

let fake_peer_mode () =
  match Sys.getenv_opt "ROCQ_SIMPLE_API_TEST_PEER" with
  | Some("startup-failure") -> fake_startup_failure ()
  | Some("cancel-failure") -> fake_cancel_failure ()
  | _ -> false

let status_to_string = function
  | Unix.WEXITED n -> Printf.sprintf "exited with code %d" n
  | Unix.WSIGNALED n -> Printf.sprintf "was killed by signal %d" n
  | Unix.WSTOPPED n -> Printf.sprintf "was stopped by signal %d" n

let run_subprocess ?(environment=Unix.environment ()) args =
  let executable = Unix.realpath Sys.executable_name in
  let argv = Array.of_list (executable :: args) in
  let pid =
    Unix.create_process_env executable argv environment Unix.stdin Unix.stdout
      Unix.stderr
  in
  match waitpid pid with
  | Unix.WEXITED 0 -> ()
  | status -> failf "subprocess %s" (status_to_string status)

let with_fake_peer mode f =
  with_temp_dir "rocq_simple_api_peer" @@ fun dir ->
  let executable = Unix.realpath Sys.executable_name in
  let peer = Filename.concat dir "rocq-simple-api.private.toplevel" in
  Unix.symlink executable peer;
  let marker = Filename.concat dir "marker" in
  let go = Filename.concat dir "go" in
  let old_path = Sys.getenv "PATH" in
  let old_mode = Sys.getenv_opt "ROCQ_SIMPLE_API_TEST_PEER" in
  let old_marker = Sys.getenv_opt "ROCQ_SIMPLE_API_TEST_PEER_MARKER" in
  let old_go = Sys.getenv_opt "ROCQ_SIMPLE_API_TEST_PEER_GO" in
  let restore name = function
    | Some(value) -> Unix.putenv name value
    | None -> Unix.putenv name ""
  in
  Fun.protect
    ~finally:(fun () ->
      Unix.putenv "PATH" old_path;
      restore "ROCQ_SIMPLE_API_TEST_PEER" old_mode;
      restore "ROCQ_SIMPLE_API_TEST_PEER_MARKER" old_marker;
      restore "ROCQ_SIMPLE_API_TEST_PEER_GO" old_go)
    (fun () ->
      Unix.putenv "PATH" (dir ^ ":" ^ old_path);
      Unix.putenv "ROCQ_SIMPLE_API_TEST_PEER" mode;
      Unix.putenv "ROCQ_SIMPLE_API_TEST_PEER_MARKER" marker;
      Unix.putenv "ROCQ_SIMPLE_API_TEST_PEER_GO" go;
      f ~marker ~go)

let test_kill_blocked_write_mode () =
  Sys.set_signal Sys.sigpipe Sys.Signal_default;
  let top = Rocq_toplevel.init ~args:[] in
  Unix.kill (-(Rocq_toplevel.get_pid top)) Sys.sigstop;
  let worker = Thread.create (fun () ->
    try
      ignore (Rocq_toplevel.run top ~loc ~text:(String.make 1_000_000 ' '))
    with _ -> ()
  ) () in
  Thread.delay 0.05;
  Rocq_toplevel.kill top;
  Thread.join worker

let test_kill_blocked_write () =
  run_subprocess ["--kill-blocked-write"]

let test_startup_descriptor_ownership () =
  with_fake_peer "startup-failure" @@ fun ~marker ~go:_ ->
  let init_result = ref None in
  let worker = Thread.create (fun () ->
    init_result := Some(try
      ignore (Rocq_toplevel.init ~args:[]);
      Ok(())
    with e -> Error(e))
  ) () in
  wait_for_file marker 5000;
  let unrelated =
    List.init 8 (fun _ -> Unix.openfile "/dev/null" [Unix.O_RDONLY] 0)
  in
  Thread.join worker;
  begin match !init_result with
  | Some(Error(_)) -> ()
  | Some(Ok(())) -> failwith "fake startup unexpectedly succeeded"
  | None -> assert false
  end;
  Fun.protect
    ~finally:(fun () -> List.iter close_fd_noerr unrelated)
    (fun () ->
      List.iter (fun fd ->
        try ignore (Unix.fstat fd) with
        | Unix.Unix_error(EBADF, _, _) ->
            failwith "startup cleanup closed an unrelated descriptor"
      ) unrelated)

let test_pending_cancellation_failure () =
  with_fake_peer "cancel-failure" @@ fun ~marker ~go ->
  let top = Rocq_toplevel.init ~args:[] in
  let request_result = ref None in
  let worker = Thread.create (fun () ->
    request_result := Some(try
      ignore (Rocq_toplevel.run top ~loc ~text:"Check I.");
      `Completed
    with
    | Rocq_toplevel.Interrupted (Rocq_toplevel.Failed error) ->
        `Interrupted(error)
    | Rocq_toplevel.Stopped (Rocq_toplevel.Failed error) ->
        `Stopped(error)
    | e -> `Raised(e))
  ) () in
  wait_for_file marker 5000;
  Rocq_toplevel.interrupt top;
  touch go;
  Thread.join worker;
  let error =
    match !request_result with
    | Some(`Interrupted(error)) -> error
    | Some(`Stopped(error)) ->
        failf "active request raised Stopped instead of Interrupted: %s"
          (Printexc.to_string error)
    | Some(`Completed) -> failwith "request unexpectedly completed"
    | Some(`Raised(error)) -> raise error
    | None -> assert false
  in
  begin try
    ignore (Rocq_toplevel.run top ~loc ~text:"Check I.");
    failwith "failed top-level accepted another request"
  with
  | Rocq_toplevel.Stopped (Rocq_toplevel.Failed later)
      when later == error -> ()
  end

let rec exhaust_descriptors acc =
  try
    let fd = Unix.openfile "/dev/null" [Unix.O_RDONLY] 0 in
    exhaust_descriptors (fd :: acc)
  with Unix.Unix_error(EMFILE, _, _) -> acc

let available_descriptor_slots () =
  let descriptors = exhaust_descriptors [] in
  let count = List.length descriptors in
  List.iter close_fd_noerr descriptors;
  count

let test_pipe_failure_mode () =
  let held = exhaust_descriptors [] in
  let held =
    match held with
    | fd1 :: fd2 :: fd3 :: rest ->
        Unix.close fd1;
        Unix.close fd2;
        Unix.close fd3;
        rest
    | _ -> failwith "descriptor limit is unexpectedly small"
  in
  Fun.protect
    ~finally:(fun () -> List.iter close_fd_noerr held)
    (fun () ->
      let before = available_descriptor_slots () in
      if before <> 3 then
        failf "expected 3 free descriptors, found %d" before;
      begin try
        ignore (Rocq_toplevel.init ~args:[]);
        failwith "initialization unexpectedly succeeded"
      with Unix.Unix_error(EMFILE, _, _) -> ()
      end;
      let after = available_descriptor_slots () in
      if after <> before then
        failf "pipe failure leaked descriptors: before=%d after=%d"
          before after)

let test_pipe_failure () =
  let executable = Unix.realpath Sys.executable_name in
  let argv =
    [|"/bin/sh"; "-c"; "ulimit -n 32; exec \"$0\" --pipe-failure";
      executable|]
  in
  let pid =
    Unix.create_process "/bin/sh" argv Unix.stdin Unix.stdout Unix.stderr
  in
  match waitpid pid with
  | Unix.WEXITED 0 -> ()
  | status -> failf "pipe-failure subprocess %s" (status_to_string status)

let run_tests () =
  Sys.set_signal Sys.sigpipe Sys.Signal_default;
  test_kill_blocked_write ();
  test_startup_descriptor_ownership ();
  test_pending_cancellation_failure ();
  test_pipe_failure ()

let () =
  if fake_peer_mode () then () else
  match Array.to_list Sys.argv with
  | [_; "--kill-blocked-write"] -> test_kill_blocked_write_mode ()
  | [_; "--pipe-failure"] -> test_pipe_failure_mode ()
  | [_] -> run_tests ()
  | _ -> failwith "unexpected test arguments"

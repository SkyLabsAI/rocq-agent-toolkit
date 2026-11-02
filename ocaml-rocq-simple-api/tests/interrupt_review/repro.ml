(* Review-only executable regression cases. No production implementation is copied
   or modified. Raw-protocol cases force legal completion/cancellation orderings. *)
open Rocq_simple_api_internal.Rocq_toplevel_data
let loc = Loc.initial Loc.ToplevelInput
let check condition message = if not condition then failwith message
let fork_ok top =
  match Rocq_toplevel.fork top with Ok child -> child | Error e -> failwith e
let exists pid = try Unix.kill pid 0; true with Unix.Unix_error (ESRCH, _, _) -> false
let alive pid =
  try
    let ic = open_in (Printf.sprintf "/proc/%d/stat" pid) in
    let line = input_line ic in
    close_in ic;
    let i = String.rindex line ')' in line.[i + 2] <> 'Z'
  with Sys_error _ -> false
let wait_until predicate =
  let deadline = Unix.gettimeofday () +. 3. in
  while not (predicate ()) && Unix.gettimeofday () < deadline do Thread.delay 0.001 done;
  check (predicate ()) "timed out waiting for condition"
let children pid =
  let path = Printf.sprintf "/proc/%d/task/%d/children" pid pid in
  let ic = open_in path in
  let text = In_channel.input_all ic in
  close_in ic;
  String.split_on_char ' ' (String.trim text)
  |> List.filter (fun s -> s <> "") |> List.map int_of_string
let protect_top f =
  let top = Rocq_toplevel.init ~args:[] in
  Fun.protect ~finally:(fun () -> try Rocq_toplevel.kill top with _ -> ())
    (fun () -> f top)

type raw = {pid : int; ic : in_channel; oc : out_channel; mutable id : int; mutable sid : int}
let raw_send raw value = Marshal.to_channel raw.oc value []; flush raw.oc
let raw_read raw = Marshal.from_channel raw.ic
let raw_open () =
  let prog = "rocq-simple-api.private.toplevel" in
  let input, output = Unix.pipe ~cloexec:true () in
  let response, writer = Unix.pipe ~cloexec:true () in
  let pid = Unix.create_process prog [|prog|] input writer Unix.stderr in
  Unix.close input; Unix.close writer;
  let ic = Unix.in_channel_of_descr response in
  let oc = Unix.out_channel_of_descr output in
  let reported, sid = Marshal.from_channel ic in
  check (reported = pid) "wrong startup PID";
  {pid; ic; oc; id = 0; sid}
let raw_close raw =
  (try Unix.kill (-raw.pid) Sys.sigkill with _ -> ());
  (try Unix.kill raw.pid Sys.sigkill with _ -> ());
  close_out_noerr raw.oc; close_in_noerr raw.ic;
  (try ignore (Unix.waitpid [] raw.pid) with _ -> ())
let with_raw f =
  let raw = raw_open () in Fun.protect ~finally:(fun () -> raw_close raw) (fun () -> f raw)
let raw_start : type r e. raw -> (r, e) cmd -> (r, e) response = fun raw command ->
  raw.id <- raw.id + 1;
  raw_send raw {request_id = raw.id; command};
  begin match (raw_read raw : (r, e) message) with
  | Started id when id = raw.id -> () | _ -> failwith "missing Started" end;
  match (raw_read raw : (r, e) message) with
  | Finished response -> response | _ -> failwith "missing Finished"
let raw_continue raw = raw_send raw (Continue raw.id)
let raw_cancel raw =
  raw_send raw (Cancel raw.id);
  Unix.kill (-raw.pid) Sys.sigint;
  raw_send raw (Cancel_signal_sent raw.id);
  match (raw_read raw : control_ack) with
  | Cancel_ack {request_id; sid} -> check (request_id = raw.id) "bad ack"; raw.sid <- sid
let raw_request : type r e. raw -> (r, e) cmd -> (r, e) result = fun raw command ->
  match raw_start raw command with
  | Completed {sid; result; _} -> raw.sid <- sid; raw_continue raw; result
  | Interrupted _ -> failwith "unexpected interruption"
let raw_run raw text = raw_request raw (Run {loc; text})
let raw_run_ok raw text = match raw_run raw text with
  | Ok _ -> () | Error (message, _) -> failwith message

let cancelled_backtrack () = with_raw (fun raw ->
  raw_run_ok raw "Definition before_backtrack := 0.";
  let earlier = raw.sid in
  raw_run_ok raw "Definition lost_after_cancel := 1.";
  let before = raw.sid in
  begin match raw_start raw (BackTo {sid = earlier}) with
  | Completed {result = Ok (); _} -> ()
  | _ -> failwith "backtrack did not complete successfully"
  end;
  raw_cancel raw;
  Printf.printf "state before=%d; acknowledged rollback=%d\n%!" before raw.sid;
  match raw_run raw "Check lost_after_cancel." with
  | Ok _ -> ()
  | Error (message, _) -> failwith ("cancelled BackTo destroyed the original state: " ^ message))

let idle_failure () = protect_top (fun top ->
  let pid = Rocq_toplevel.get_pid top in
  Unix.kill (-pid) Sys.sigkill;
  wait_until (fun () -> not (alive pid));
  try
    ignore (Rocq_toplevel.run top ~loc ~text:"Check I.");
    failwith "operation on dead child succeeded"
  with Rocq_toplevel.Interrupted (Failed _) -> print_endline "failure correctly reported")

let fork_kill_stopped_supervisor ~active () = protect_top (fun parent ->
  let child = fork_ok parent in
  let pid = Rocq_toplevel.get_pid child in
  let ic = open_in (Printf.sprintf "/proc/%d/stat" pid) in
  let stat = input_line ic in close_in ic;
  let rest = String.sub stat (String.rindex stat ')' + 2)
    (String.length stat - String.rindex stat ')' - 2) in
  let supervisor = int_of_string (List.nth (String.split_on_char ' ' rest) 1) in
  let worker = if not active then None else begin
    List.iter (fun text -> match Rocq_toplevel.run child ~loc ~text with
      | Ok _ -> () | Error (message, _) -> failwith message) ["Goal True."; "Proof."];
    let worker = Thread.create (fun () ->
      try ignore (Rocq_toplevel.run child ~loc ~text:"let rec loop := loop in loop.")
      with Rocq_toplevel.Interrupted Killed -> ()) () in
    wait_until (fun () -> try ignore (Rocq_toplevel.StateID.current child); false
      with Rocq_toplevel.Busy -> true);
    Some worker
  end in
  Unix.kill supervisor Sys.sigstop;
  Fun.protect ~finally:(fun () -> Unix.kill supervisor Sys.sigcont;
    (try Rocq_toplevel.kill child with _ -> ()); wait_until (fun () -> not (exists pid))) (fun () ->
    match worker with
    | None ->
        Rocq_toplevel.kill child;
        Printf.printf "kill returned; forked PID %d still running=%b\n%!" pid (alive pid);
        check (not (alive pid)) "kill returned without killing the forked toplevel"
    | Some worker ->
        let done_ = Atomic.make false in
        let rescue_needed = Atomic.make false in
        let rescuer = Thread.create (fun () -> Thread.delay 0.3;
          Atomic.set rescue_needed (not (Atomic.get done_));
          Unix.kill supervisor Sys.sigcont) () in
        let start = Unix.gettimeofday () in
        Rocq_toplevel.kill child;
        Atomic.set done_ true;
        let elapsed = Unix.gettimeofday () -. start in
        Thread.join rescuer; Thread.join worker;
        Printf.printf "kill waited %.3fs; needed external supervisor SIGCONT=%b\n%!"
          elapsed (Atomic.get rescue_needed);
        check (not (Atomic.get rescue_needed)) "hard kill hung until the supervisor was externally resumed"))

let split_cancel_reap () = with_raw (fun raw ->
  let text = String.concat "" (List.init 200_000 (fun _ -> "Check I. ")) in
  raw.id <- raw.id + 1;
  raw_send raw {request_id = raw.id; command = Split {loc; text; sid = None}};
  ignore (raw_read raw : (raw_split_data, empty) message);
  wait_until (fun () -> children raw.pid <> []);
  raw_send raw (Cancel raw.id); Unix.kill (-raw.pid) Sys.sigint;
  raw_send raw (Cancel_signal_sent raw.id);
  ignore (raw_read raw : (raw_split_data, empty) message);
  ignore (raw_read raw : control_ack);
  check (children raw.pid = []) "split cancellation left a child behind")

let split_fork_window ~check_protocol () =
  let marker = Filename.temp_file "rocq-review-fork-window" "" in
  Sys.remove marker;
  Unix.putenv "ROCQ_REVIEW_MARKER" marker;
  Fun.protect ~finally:(fun () ->
    (try Sys.remove marker with _ -> ());
    (try Sys.remove (marker ^ ".release") with _ -> ())) (fun () ->
    protect_top (fun top ->
      let pid = Rocq_toplevel.get_pid top in
      let fds_before = Array.length (Sys.readdir (Printf.sprintf "/proc/%d/fd" pid)) in
      let result = ref None in
      let text = String.concat "" (List.init 200_000 (fun _ -> "Check I. ")) in
      let worker = Thread.create (fun () ->
        result := Some (try ignore (Rocq_toplevel.split top ~loc ~text); None
          with e -> Some e)) () in
      wait_until (fun () -> Sys.file_exists marker);
      Rocq_toplevel.interrupt top;
      if check_protocol then close_out (open_out (marker ^ ".release"))
      else Sys.remove marker;
      Thread.join worker;
      begin match Option.get !result with
      | Some (Rocq_toplevel.Interrupted Interrupt) -> ()
      | Some e -> raise e
      | None -> failwith "missing cooperative interruption"
      end;
      if check_protocol then begin
        (* The helper can acknowledge cancellation first. Allow the original
           owner to resume and publish its duplicate terminal response. *)
        Thread.delay 0.2;
        try match Rocq_toplevel.run top ~loc ~text:"Check I." with
        | Ok _ -> () | Error (message, _) -> failwith message
        with Rocq_toplevel.Interrupted (Failed e) ->
          failwith ("next request after interruption failed: " ^ Printexc.to_string e)
      end;
      let remaining = children pid in
      let fds_after = Array.length (Sys.readdir (Printf.sprintf "/proc/%d/fd" pid)) in
      Printf.printf "remaining splitter children: %s; fd count %d -> %d\n%!"
        (String.concat " " (List.map string_of_int remaining)) fds_before fds_after;
      check (remaining = []) "interruption between fork and cleanup registration leaked the splitter"))

let split_signal_boundary () = protect_top (fun top ->
  let pid = Rocq_toplevel.get_pid top in
  let text = if Sys.getenv "ROCQ_REVIEW_SCHEDULE" = "after-fork" then
    String.concat "" (List.init 200_000 (fun _ -> "Check I. ")) else "Check I." in
  let interrupted =
    try ignore (Rocq_toplevel.split top ~loc ~text); false with
    | Rocq_toplevel.Interrupted Interrupt -> true
    | Rocq_toplevel.Interrupted (Failed e) ->
        failwith ("cooperative SIGINT killed the toplevel: " ^ Printexc.to_string e)
  in
  check interrupted "missing cooperative interruption";
  let remaining = children pid in
  Printf.printf "remaining splitter children: %s\n%!"
    (String.concat " " (List.map string_of_int remaining));
  check (remaining = []) "interruption between fork and cleanup registration leaked the splitter")

let kill_during_stop () = protect_top (fun top ->
  let pid = Rocq_toplevel.get_pid top in
  Unix.kill pid Sys.sigstop;
  let stopping = Thread.create (fun () -> Rocq_toplevel.stop top) () in
  wait_until (fun () -> try ignore (Rocq_toplevel.get_pid top); false with
    Rocq_toplevel.Stopped Normal -> true);
  (* A rescuer keeps this reproducer bounded; omit it and kill never returns. *)
  let rescuer = Thread.create (fun () -> Thread.delay 0.3; Unix.kill pid Sys.sigcont) () in
  let start = Unix.gettimeofday () in
  let result = try Rocq_toplevel.kill top; "killed" with
    Rocq_toplevel.Stopped Normal -> "gracefully stopped" in
  let elapsed = Unix.gettimeofday () -. start in
  Thread.join rescuer; Thread.join stopping;
  Printf.printf "kill waited %.3fs for external SIGCONT, result=%s\n%!" elapsed result;
  check (result = "killed") "kill cannot force termination while stop is waiting")

let startup_fd_reuse () =
  let source = Filename.temp_file "rocq-review-startup" ".v" in
  let marker = Filename.temp_file "rocq-review-ready" "" in
  Sys.remove marker;
  let oc = open_out source in
  Printf.fprintf oc "Redirect %S Check I.\nGoal True.\nlet rec loop := loop in loop.\n" marker;
  close_out oc;
  Fun.protect ~finally:(fun () -> Sys.remove source;
    (try Sys.remove (marker ^ ".out") with _ -> ())) (fun () ->
    let startup_result = ref None in
    let worker = Thread.create (fun () ->
      startup_result := Some (try ignore (Rocq_toplevel.init ~args:["-l"; source]); "success"
        with e -> Printexc.to_string e)) () in
    wait_until (fun () -> Sys.file_exists (marker ^ ".out"));
    let tasks = Printf.sprintf "/proc/%d/task" (Unix.getpid ()) in
    let pids = Sys.readdir tasks |> Array.to_list |> List.concat_map (fun tid ->
      let ic = open_in (Filename.concat (Filename.concat tasks tid) "children") in
      let text = In_channel.input_all ic in close_in ic;
      String.split_on_char ' ' (String.trim text) |> List.filter (fun s -> s <> "")
      |> List.map int_of_string) in
    let pid = List.hd pids in
    let fd = Unix.openfile "/dev/null" [Unix.O_RDONLY] 0 in
    Unix.kill pid Sys.sigkill;
    Thread.join worker;
    Printf.printf "startup result=%s\n%!" (Option.get !startup_result);
    let valid = try ignore (Unix.fstat fd); true with
      Unix.Unix_error (EBADF, _, _) -> false in
    if valid then Unix.close fd;
    check valid "startup failure closed a descriptor owned by another thread")

let deferred_cancel_failure ~ignore_sigpipe () =
  (* Ignore SIGPIPE to inspect the exception contract independently of the
     separate SIGPIPE regression. The other case keeps the default disposition. *)
  if ignore_sigpipe then Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  protect_top (fun top ->
    let pid = Rocq_toplevel.get_pid top in
    Unix.kill pid Sys.sigstop;
    let result = ref None in
    let text = String.make 8_000_000 ' ' in
    let worker = Thread.create (fun () ->
      result := Some (try ignore (Rocq_toplevel.loc_after_blanks top ~loc ~text); None
        with e -> Some e)) () in
    wait_until (fun () -> try ignore (Rocq_toplevel.StateID.current top); false
      with Rocq_toplevel.Busy -> true);
    Rocq_toplevel.interrupt top;
    Unix.kill pid Sys.sigcont;
    Thread.join worker;
    match Option.get !result with
    | Some (Rocq_toplevel.Interrupted (Failed _)) -> ()
    | Some e -> failwith ("active operation raised " ^ Printexc.to_string e ^
        " instead of Interrupted (Failed _)")
    | None -> failwith "operation unexpectedly succeeded")

let kill_blocked_writer () = protect_top (fun top ->
  Unix.kill (Rocq_toplevel.get_pid top) Sys.sigstop;
  let result = ref None in
  let text = String.make 1_000_000 ' ' in
  let worker = Thread.create (fun () ->
    result := Some (try ignore (Rocq_toplevel.run top ~loc ~text); None
      with e -> Some e)) () in
  wait_until (fun () -> try ignore (Rocq_toplevel.StateID.current top); false
    with Rocq_toplevel.Busy -> true);
  Thread.delay 0.05;
  Rocq_toplevel.kill top;
  Thread.join worker;
  match Option.get !result with
  | Some (Rocq_toplevel.Interrupted Killed) -> ()
  | Some e -> raise e
  | None -> failwith "killed request unexpectedly succeeded")

let guard_cloexec () =
  let marker = Filename.temp_file "rocq-review-cloexec" "" in
  Sys.remove marker;
  Unix.putenv "ROCQ_REVIEW_MARKER" marker;
  Unix.putenv "ROCQ_REVIEW_API_PID" (string_of_int (Unix.getpid ()));
  Fun.protect ~finally:(fun () -> try Sys.remove marker with _ -> ()) (fun () ->
    protect_top (fun parent ->
      (* Launch concurrently in another domain while the scheduling hook holds
         the actual FIFO open before returning control to OCaml. *)
      let forking = Domain.spawn (fun () -> fork_ok parent) in
      wait_until (fun () -> Sys.file_exists marker);
      let unrelated = Rocq_toplevel.init ~args:[] in
      Sys.remove marker;
      let child = Domain.join forking in
      let pid = Rocq_toplevel.get_pid child in
      Rocq_toplevel.stop child;
      Thread.delay 0.15;
      let held_open = alive pid in
      Rocq_toplevel.stop unrelated;
      wait_until (fun () -> not (exists pid));
      Printf.printf "forked child alive after stop=%b; after unrelated top stops=%b\n%!"
        held_open (alive pid);
      check (not held_open) "a concurrently spawned process inherited the FIFO guard and prevented EOF"))

let second_pipe_failure () =
  let rec fill acc =
    match Unix.openfile "/dev/null" [Unix.O_RDONLY] 0 with
    | fd -> fill (fd :: acc)
    | exception Unix.Unix_error (EMFILE, _, _) -> acc
  in
  let held = fill [] in
  let released, held = match held with a :: b :: c :: rest -> [a; b; c], rest
    | _ -> failwith "not enough descriptor slots" in
  List.iter Unix.close released;
  Fun.protect ~finally:(fun () -> List.iter Unix.close held) (fun () ->
    let available () = let fds = fill [] in
      let count = List.length fds in List.iter Unix.close fds; count in
    let before = available () in
    (try ignore (Rocq_toplevel.init ~args:[]); failwith "init unexpectedly succeeded"
     with Unix.Unix_error (EMFILE, _, _) -> ());
    let after = available () in
    Printf.printf "available descriptor slots before init=%d; after=%d\n%!" before after;
    check (before = after) "second pipe allocation failure leaked the first pipe")

let fork_pipe_failure () = protect_top (fun top ->
  let pid = Rocq_toplevel.get_pid top in
  (* Lower the real private process's limit after initialization. Existing
     descriptors stay valid, but it cannot allocate the new PID-report pipe. *)
  let limiter = Unix.create_process "prlimit"
    [|"prlimit"; "--pid"; string_of_int pid; "--nofile=3:3"|]
    Unix.stdin Unix.stdout Unix.stderr in
  check (snd (Unix.waitpid [] limiter) = Unix.WEXITED 0) "prlimit failed";
  try match Rocq_toplevel.fork top with
  | Error message -> Printf.printf "recoverable fork error: %s\n%!" message
  | Ok child -> Rocq_toplevel.kill child; failwith "fork unexpectedly succeeded"
  with Rocq_toplevel.Interrupted (Failed e) ->
    failwith ("fork resource error killed the source toplevel: " ^ Printexc.to_string e))

let backtrack_ignores_interrupt () = protect_top (fun top ->
  let run text = match Rocq_toplevel.run top ~loc ~text with
    | Ok _ -> () | Error (message, _) -> failwith message in
  run "Definition before_backtrack := 0.";
  let sid = Rocq_toplevel.StateID.current top in
  run "Definition after_backtrack := 1.";
  let pid = Rocq_toplevel.get_pid top in
  Unix.kill pid Sys.sigstop;
  let result = ref None in
  let worker = Thread.create (fun () ->
    result := Some (try Rocq_toplevel.back_to top ~sid with e ->
      Error (Printexc.to_string e))) () in
  wait_until (fun () -> try ignore (Rocq_toplevel.StateID.current top); false
    with Rocq_toplevel.Busy -> true);
  Rocq_toplevel.interrupt top;
  Unix.kill pid Sys.sigcont;
  Thread.join worker;
  begin match Option.get !result with Ok () -> () | Error e -> failwith e end;
  run "Check before_backtrack.";
  match Rocq_toplevel.run top ~loc ~text:"Check after_backtrack." with
  | Error _ -> print_endline "BackTo ignored cooperative interrupt and completed normally"
  | Ok _ -> failwith "backtrack did not take effect")

let cancelled_reset () = with_raw (fun raw ->
  raw_run_ok raw "Definition before_reset := 0.";
  raw_run_ok raw "Definition lost_after_reset := 1.";
  begin match raw_start raw (Run {loc; text = "Reset lost_after_reset."}) with
  | Completed {result = Ok _; _} -> ()
  | Completed {result = Error (message, _); _} -> failwith message
  | _ -> failwith "unexpected interruption"
  end;
  try raw_cancel raw; raw_run_ok raw "Check lost_after_reset." with End_of_file ->
    failwith "cancelling a completed Run Reset killed the private process during rollback")

let () =
  match Sys.argv.(1) with
  | "cancelled-backtrack" -> cancelled_backtrack ()
  | "idle-failure" -> idle_failure ()
  | "fork-kill-stopped-supervisor" -> fork_kill_stopped_supervisor ~active:true ()
  | "fork-kill-idle-stopped-supervisor" -> fork_kill_stopped_supervisor ~active:false ()
  | "split-cancel-reap" -> split_cancel_reap ()
  | "split-signal-boundary" -> split_signal_boundary ()
  | "split-fork-window" -> split_fork_window ~check_protocol:false ()
  | "split-protocol-corruption" -> split_fork_window ~check_protocol:true ()
  | "kill-during-stop" -> kill_during_stop ()
  | "startup-fd-reuse" -> startup_fd_reuse ()
  | "deferred-cancel-failure" -> deferred_cancel_failure ~ignore_sigpipe:true ()
  | "cancel-sigpipe" -> deferred_cancel_failure ~ignore_sigpipe:false ()
  | "kill-blocked-writer" -> kill_blocked_writer ()
  | "guard-cloexec" -> guard_cloexec ()
  | "second-pipe-failure" -> second_pipe_failure ()
  | "fork-pipe-failure" -> fork_pipe_failure ()
  | "backtrack-ignores-interrupt" -> backtrack_ignores_interrupt ()
  | "cancelled-reset" -> cancelled_reset ()
  | name -> failwith ("unknown case: " ^ name)

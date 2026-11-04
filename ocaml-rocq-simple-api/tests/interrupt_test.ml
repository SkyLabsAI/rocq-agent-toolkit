let loc = Loc.initial Loc.ToplevelInput

type outcome =
  | Completed
  | Interrupted of Rocq_toplevel.interrupted_reason
  | Stopped of Rocq_toplevel.stopped_reason
  | Busy
  | Raised of exn

let outcome f =
  try f (); Completed with
  | Rocq_toplevel.Interrupted reason -> Interrupted reason
  | Rocq_toplevel.Stopped reason -> Stopped reason
  | Rocq_toplevel.Busy -> Busy
  | e -> Raised(e)

let run top text =
  outcome (fun () -> ignore (Rocq_toplevel.run top ~loc ~text))

let split top text =
  outcome (fun () -> ignore (Rocq_toplevel.split top ~loc ~text))

let stopped_reason_to_string : Rocq_toplevel.stopped_reason -> string =
  function
  | Normal -> "normal"
  | Killed -> "killed"
  | Failed(e) -> "failed: " ^ Printexc.to_string e

let interrupted_reason_to_string :
    Rocq_toplevel.interrupted_reason -> string = function
  | Interrupt -> "interrupt"
  | Killed -> "killed"
  | Failed(e) -> "failed: " ^ Printexc.to_string e

let fail_outcome = function
  | Raised(e) -> raise e
  | Completed -> failwith "operation unexpectedly completed"
  | Interrupted(reason) ->
      failwith ("operation was unexpectedly interrupted (" ^
        interrupted_reason_to_string reason ^ ")")
  | Stopped(reason) ->
      failwith ("operation was unexpectedly stopped (" ^
        stopped_reason_to_string reason ^ ")")
  | Busy -> failwith "operation was unexpectedly busy"

let assert_outcome expected outcome =
  if outcome <> expected then fail_outcome outcome

let run_ok top text =
  match Rocq_toplevel.run top ~loc ~text with
  | Ok(_) -> ()
  | Error(s, _) -> failwith s

let back_to top sid =
  outcome @@ fun () ->
  match Rocq_toplevel.back_to top ~sid with
  | Ok(()) -> ()
  | Error(s) -> failwith s

let process_exists pid =
  try Unix.kill pid 0; true with
  | Unix.Unix_error(ESRCH, _, _) -> false

let rec wait_for_process_exit pid attempts =
  if not (process_exists pid) then () else if attempts = 0 then
    failwith "process was not reaped"
  else begin
    Thread.delay 0.01;
    wait_for_process_exit pid (attempts - 1)
  end

let run_cooperative_interrupt top operation =
  let result = ref None in
  let done_ = Atomic.make false in
  let worker = Thread.create (fun () ->
    result := Some(operation ());
    Atomic.set done_ true
  ) () in
  let rec interrupt_until_done attempts =
    if Atomic.get done_ then () else if attempts = 0 then begin
      Rocq_toplevel.kill top;
      Thread.join worker;
      failwith "cooperative interruption timed out"
    end else begin
      Rocq_toplevel.interrupt top;
      Thread.delay 0.01;
      interrupt_until_done (attempts - 1)
    end
  in
  interrupt_until_done 500;
  Thread.join worker;
  Option.get !result

let run_kill top text =
  let result = ref None in
  let pid = Rocq_toplevel.get_pid top in
  let worker = Thread.create (fun () ->
    result := Some(run top text)
  ) () in
  Thread.delay 0.05;
  Unix.kill (-pid) Sys.sigstop;
  Rocq_toplevel.kill top;
  Thread.join worker;
  (Option.get !result, pid)

let test_initial () =
  let top = Rocq_toplevel.init ~args:[] in
  Rocq_toplevel.interrupt top;
  run_ok top "Goal True.";
  run_ok top "Proof.";
  assert_outcome (Interrupted Rocq_toplevel.Interrupt)
    (run_cooperative_interrupt top
      (fun () -> run top "let rec loop := loop in loop."));
  run_ok top "exact I.";
  run_ok top "Qed.";
  Rocq_toplevel.stop top;
  assert_outcome (Stopped Rocq_toplevel.Normal)
    (outcome (fun () -> Rocq_toplevel.interrupt top));
  assert_outcome (Stopped Rocq_toplevel.Normal) (run top "Check I.")

let test_fork () =
  let parent = Rocq_toplevel.init ~args:[] in
  run_ok parent "Definition before_fork := 0.";
  let child =
    match Rocq_toplevel.fork parent with
    | Ok(child) -> child
    | Error(s) -> failwith s
  in
  run_ok child "Goal True.";
  run_ok child "Proof.";
  assert_outcome (Interrupted Rocq_toplevel.Interrupt)
    (run_cooperative_interrupt child
      (fun () -> run child "let rec loop := loop in loop."));
  run_ok child "Abort.";
  run_ok child "Check before_fork.";
  run_ok parent "Check before_fork.";
  let child_pid = Rocq_toplevel.get_pid child in
  Rocq_toplevel.stop child;
  wait_for_process_exit child_pid 100;
  Rocq_toplevel.stop parent

let test_fork_supervisor () =
  let parent = Rocq_toplevel.init ~args:[] in
  let child =
    match Rocq_toplevel.fork parent with
    | Ok(child) -> child
    | Error(s) -> failwith s
  in
  let parent_pid = Rocq_toplevel.get_pid parent in
  let child_pid = Rocq_toplevel.get_pid child in
  Rocq_toplevel.kill parent;
  if process_exists parent_pid then
    failwith "the source toplevel was not reaped";
  run_ok child "Check I.";
  Unix.kill (-child_pid) Sys.sigkill;
  Thread.delay 0.05;
  Rocq_toplevel.kill child;
  wait_for_process_exit child_pid 100

let test_split () =
  let top = Rocq_toplevel.init ~args:[] in
  let text =
    let buffer = Buffer.create 2_000_000 in
    for _ = 1 to 200_000 do Buffer.add_string buffer "Check I. " done;
    Buffer.contents buffer
  in
  assert_outcome (Interrupted Rocq_toplevel.Interrupt)
    (run_cooperative_interrupt top (fun () -> split top text));
  run_ok top "Check I.";
  Rocq_toplevel.stop top

let test_completion_race () =
  let top = Rocq_toplevel.init ~args:[] in
  for _ = 1 to 20 do
    let result = ref None in
    let done_ = Atomic.make false in
    let worker = Thread.create (fun () ->
      result := Some(run top "Check I.");
      Atomic.set done_ true
    ) () in
    for _ = 1 to 20 do
      if not (Atomic.get done_) then Rocq_toplevel.interrupt top;
      Thread.yield ()
    done;
    Thread.join worker;
    begin match Option.get !result with
    | Completed | Interrupted Rocq_toplevel.Interrupt -> ()
    | Interrupted Rocq_toplevel.Killed ->
        failwith "completion race unexpectedly killed the toplevel"
    | Interrupted (Rocq_toplevel.Failed e) -> raise e
    | Stopped _ -> failwith "completion race unexpectedly stopped"
    | Busy -> failwith "completion race unexpectedly reported busy"
    | Raised(e) -> raise e
    end;
    run_ok top "Check I."
  done;
  Rocq_toplevel.stop top

let test_back_to_not_interruptible () =
  let top = Rocq_toplevel.init ~args:[] in
  let sid = Rocq_toplevel.StateID.current top in
  run_ok top "Definition after_backtrack := 0.";
  let pid = Rocq_toplevel.get_pid top in
  Unix.kill pid Sys.sigstop;
  let result = ref None in
  let worker = Thread.create (fun () ->
    result := Some(back_to top sid)
  ) () in
  let rec wait_until_busy attempts =
    match outcome (fun () -> ignore (Rocq_toplevel.StateID.current top)) with
    | Busy -> ()
    | Completed when attempts > 0 ->
        Thread.delay 0.001;
        wait_until_busy (attempts - 1)
    | Completed -> failwith "back_to did not start"
    | result -> fail_outcome result
  in
  let interrupt_result =
    Fun.protect ~finally:(fun () -> Unix.kill pid Sys.sigcont) @@ fun () ->
    wait_until_busy 500;
    outcome (fun () -> Rocq_toplevel.interrupt top)
  in
  Thread.join worker;
  assert_outcome Completed interrupt_result;
  assert_outcome Completed (Option.get !result);
  let current = Rocq_toplevel.StateID.current top in
  let current = Rocq_toplevel.StateID.to_int top current in
  let expected = Rocq_toplevel.StateID.to_int top sid in
  if current <> expected then failwith "back_to reached the wrong state";
  run_ok top "Check I.";
  Rocq_toplevel.stop top

let test_busy () =
  let top = Rocq_toplevel.init ~args:[] in
  run_ok top "Goal True.";
  run_ok top "Proof.";
  let sid = Rocq_toplevel.StateID.current top in
  let result = ref None in
  let worker = Thread.create (fun () ->
    result := Some(run top "let rec loop := loop in loop.")
  ) () in
  Thread.delay 0.05;
  let assert_busy f = assert_outcome Busy (outcome f) in
  assert_busy (fun () ->
    ignore (Rocq_toplevel.run top ~loc ~text:"Check I."));
  assert_busy (fun () -> ignore (Rocq_toplevel.back_to top ~sid));
  assert_busy (fun () -> ignore (Rocq_toplevel.StateID.current top));
  assert_busy (fun () -> Rocq_toplevel.stop top);
  assert_busy (fun () -> ignore (Rocq_toplevel.fork top));
  assert_busy (fun () ->
    ignore (Rocq_toplevel.loc_after_blanks top ~loc ~text:""));
  assert_busy (fun () -> ignore (Rocq_toplevel.structured_goals top));
  assert_busy (fun () -> ignore (Rocq_toplevel.split top ~loc ~text:""));
  Rocq_toplevel.interrupt top;
  Thread.join worker;
  assert_outcome (Interrupted Rocq_toplevel.Interrupt) (Option.get !result);
  run_ok top "Abort.";
  Rocq_toplevel.stop top

let test_kill_idle () =
  let top = Rocq_toplevel.init ~args:[] in
  run_ok top "Check I.";
  let pid = Rocq_toplevel.get_pid top in
  Rocq_toplevel.kill top;
  assert_outcome (Stopped Rocq_toplevel.Killed)
    (outcome (fun () -> Rocq_toplevel.interrupt top));
  assert_outcome (Stopped Rocq_toplevel.Killed) (run top "Check I.");
  if process_exists pid then failwith "kill did not reap an idle toplevel"

let test_kill () =
  let top = Rocq_toplevel.init ~args:[] in
  run_ok top "Goal True.";
  run_ok top "Proof.";
  let (result, pid) = run_kill top "let rec loop := loop in loop." in
  assert_outcome (Interrupted Rocq_toplevel.Killed) result;
  assert_outcome (Stopped Rocq_toplevel.Killed) (run top "Check I.");
  assert_outcome (Stopped Rocq_toplevel.Killed)
    (outcome (fun () -> Rocq_toplevel.kill top));
  if process_exists pid then
    failwith "kill did not reap the private toplevel"

let test_failure () =
  let top = Rocq_toplevel.init ~args:[] in
  run_ok top "Goal True.";
  run_ok top "Proof.";
  let result = ref None in
  let pid = Rocq_toplevel.get_pid top in
  let worker = Thread.create (fun () ->
    result := Some(run top "let rec loop := loop in loop.")
  ) () in
  Thread.delay 0.05;
  Unix.kill (-pid) Sys.sigkill;
  Thread.join worker;
  let failure =
    match Option.get !result with
    | Interrupted (Rocq_toplevel.Failed e) -> e
    | outcome -> fail_outcome outcome
  in
  begin match run top "Check I." with
  | Stopped (Rocq_toplevel.Failed e) when e == failure -> ()
  | outcome -> fail_outcome outcome
  end;
  if process_exists pid then
    failwith "failure cleanup did not reap the private toplevel"

let () =
  test_initial ();
  test_fork ();
  test_fork_supervisor ();
  test_split ();
  test_completion_race ();
  test_back_to_not_interruptible ();
  test_busy ();
  test_kill_idle ();
  test_kill ();
  test_failure ()

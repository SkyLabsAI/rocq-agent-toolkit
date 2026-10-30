type outcome =
  | Completed
  | Interrupted of Rocq_toplevel.interrupted_reason
  | Raised of exn

let stop_noerr d =
  try Document.stop d with _ -> ()

let with_document f =
  let d = Document.init ~args:[] ~file:"document_interrupt_test.v" in
  Fun.protect ~finally:(fun () -> stop_noerr d) (fun () -> f d)

let run d text =
  try
    ignore (Document.insert_command d ~text);
    Completed
  with
  | Document.Interrupted(reason) -> Interrupted(reason)
  | e -> Raised(e)

let reason_to_string : Rocq_toplevel.interrupted_reason -> string =
  function
  | Interrupt -> "interrupt"
  | Killed -> "killed"
  | Failed(e) -> "failed: " ^ Printexc.to_string e

let fail_outcome = function
  | Completed -> failwith "operation unexpectedly completed"
  | Interrupted(reason) ->
      failwith ("unexpected interruption: " ^ reason_to_string reason)
  | Raised(e) -> raise e

let assert_interrupted expected = function
  | Interrupted(reason) when reason = expected -> ()
  | outcome -> fail_outcome outcome

let rec wait_and_apply result apply attempts =
  match Atomic.get result with
  | Some(outcome) -> outcome
  | None when attempts = 0 -> failwith "document operation timed out"
  | None ->
      apply ();
      Thread.delay 0.01;
      wait_and_apply result apply (attempts - 1)

let run_in_thread d text apply =
  let result = Atomic.make None in
  let worker = Thread.create (fun () ->
    Atomic.set result (Some(run d text))
  ) () in
  Thread.delay 0.05;
  let outcome = wait_and_apply result apply 500 in
  Thread.join worker;
  outcome

let run_ok d text =
  match Document.insert_command d ~text with
  | Ok(_) -> ()
  | Error(s, _) -> failwith s

let check_i d =
  run_ok d "Check I."

let prepare_loop d =
  run_ok d "Goal True.";
  Document.insert_blanks d ~text:"\n";
  run_ok d "Proof.";
  Document.insert_blanks d ~text:"\n"

let test_idle_interrupt () =
  with_document @@ fun d ->
  if Document.interrupt d then
    failwith "idle interrupt reported an active operation";
  if Document.kill d then
    failwith "idle kill reported an active operation";
  check_i d

let test_cooperative_interrupt () =
  with_document @@ fun d ->
  let working = Document.clone d in
  Fun.protect ~finally:(fun () -> stop_noerr working) @@ fun () ->
  prepare_loop working;
  let text = "let rec loop := loop in loop." in
  let apply () = ignore (Document.interrupt working) in
  let outcome = run_in_thread working text apply in
  assert_interrupted Rocq_toplevel.Interrupt outcome;
  check_i d

let test_reuse_after_interrupt () =
  with_document @@ fun d ->
  prepare_loop d;
  let text = "let rec loop := loop in loop." in
  let apply () = ignore (Document.interrupt d) in
  let outcome = run_in_thread d text apply in
  assert_interrupted Rocq_toplevel.Interrupt outcome;
  run_ok d "exact I.";
  Document.insert_blanks d ~text:"\n";
  run_ok d "Qed."

let test_interruption_during_rollback () =
  with_document @@ fun d ->
  prepare_loop d;
  let initial_index = Document.cursor_index d in
  let result = Atomic.make None in
  let worker = Thread.create (fun () ->
    let outcome =
      try
        Document.with_rollback d @@ fun () ->
        run_ok d "idtac.";
        Document.insert_blanks d ~text:"\n";
        ignore (Document.insert_command d
          ~text:"let rec loop := loop in loop.");
        Completed
      with
      | Document.Interrupted(reason) -> Interrupted(reason)
      | e -> Raised(e)
    in
    Atomic.set result (Some(outcome))
  ) () in
  Thread.delay 0.05;
  let apply () = ignore (Document.interrupt d) in
  let outcome = wait_and_apply result apply 500 in
  Thread.join worker;
  assert_interrupted Rocq_toplevel.Interrupt outcome;
  if Document.cursor_index d <> initial_index then
    failwith "with_rollback retained changes after interruption";
  run_ok d "exact I.";
  Document.insert_blanks d ~text:"\n";
  run_ok d "Qed."

let test_run_steps_interrupt_as_error () =
  with_document @@ fun d ->
  prepare_loop d;
  let initial_index = Document.cursor_index d in
  let text = "idtac.\nlet rec loop := loop in loop." in
  begin match Document.replace_suffix ~count:0 d ~text with
  | (_, Ok(())) -> ()
  | (_, Error(s, _)) -> failwith s
  end;
  let result = Atomic.make None in
  let worker = Thread.create (fun () ->
    let response = Document.run_steps ~interrupt_as_error:true d ~count:3 in
    Atomic.set result (Some(response))
  ) () in
  Thread.delay 0.05;
  let apply () = ignore (Document.interrupt d) in
  let (data, response) = wait_and_apply result apply 500 in
  Thread.join worker;
  begin match response with
  | Error(message, (2, Some(inner, _)))
      when String.ends_with ~suffix:"User interrupt." message &&
           String.ends_with ~suffix:"User interrupt." inner -> ()
  | Error(s, (count, error)) ->
      let detail =
        match error with
        | None -> "none"
        | Some(message, _) -> Printf.sprintf "%S" message
      in
      failwith (Printf.sprintf
        "unexpected interruption result: %S after %d (%s)" s count detail)
  | Ok(()) -> failwith "run_steps unexpectedly completed"
  end;
  if List.length data <> 2 then
    failwith "run_steps lost successfully processed item data";
  if Document.cursor_index d <> initial_index + 2 then
    failwith "interrupted item advanced the document cursor";
  begin match Document.dump d with
  | `Assoc(fields) ->
      begin match List.assoc_opt "rev_processed" fields with
      | Some(`List(items)) when List.length items = initial_index + 2 -> ()
      | _ -> failwith "backend recorded an unacknowledged command"
      end
  | _ -> failwith "unexpected document dump"
  end;
  Document.clear_suffix d;
  run_ok d "exact I.";
  Document.insert_blanks d ~text:"\n";
  run_ok d "Qed."

let test_kill_and_restart () =
  with_document @@ fun d ->
  let working = Document.clone d in
  Fun.protect ~finally:(fun () -> stop_noerr working) @@ fun () ->
  prepare_loop working;
  let text = "let rec loop := loop in loop." in
  let apply () = ignore (Document.kill working) in
  let outcome = run_in_thread working text apply in
  assert_interrupted Rocq_toplevel.Killed outcome;
  Document.stop working;
  Document.restart d;
  check_i d

let test_rollback_on_exception () =
  with_document @@ fun d ->
  begin match Document.with_rollback d (fun () ->
    match Document.insert_command d ~text:"Definition rolled_back := 0." with
    | Error(s, _) -> failwith s
    | Ok(_) -> raise Exit)
  with
  | exception Exit -> ()
  | _ -> failwith "with_rollback did not preserve the exception"
  end;
  begin match Document.insert_command d ~text:"Check rolled_back." with
  | Error(_) -> ()
  | Ok(_) -> failwith "with_rollback did not restore the backend state"
  end

let () =
  test_idle_interrupt ();
  test_cooperative_interrupt ();
  test_reuse_after_interrupt ();
  test_interruption_during_rollback ();
  test_run_steps_interrupt_as_error ();
  test_kill_and_restart ();
  test_rollback_on_exception ()

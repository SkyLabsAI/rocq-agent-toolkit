type state = {
  toplevels : (int, Rocq_toplevel.toplevel) Hashtbl.t;
  mutable next : int;
  mutable cur_index : int;
  mutable cur_toplevel : Rocq_toplevel.toplevel;
}

let notify fmt =
  Printf.printf (fmt ^^ "\n%!")

let output_json oc json =
  Yojson.Safe.pretty_to_channel ~std:true oc json

let run toplevel off text =
  match Rocq_toplevel.run toplevel ~off ~text with
  | Ok(data) ->
      let json = Rocq_toplevel.run_data_to_yojson data in
      notify "%a" output_json json
  | Error(s, data) ->
      let json = Rocq_toplevel.run_error_to_yojson data in
      notify "Error: while processing the command.\n%s\n%a" s output_json json

let back_to toplevel sid =
  let sid = Rocq_toplevel.StateID.unsafe_of_int toplevel sid in
  match Rocq_toplevel.back_to toplevel ~sid with
  | Error(s) -> notify "Error while processing the command.\n%s" s
  | Ok(())   -> ()

let switch state i =
  match Hashtbl.find_opt state.toplevels i with
  | None           -> notify "Error: no toplevel %i." i
  | Some(toplevel) ->
  state.cur_index <- i;
  state.cur_toplevel <- toplevel

let stop state i =
  match state.cur_index = i with
  | true  -> notify "Error: cannot stop the current toplevel."
  | false ->
  match Hashtbl.find_opt state.toplevels i with
  | None           -> notify "Error: no toplevel %i." i
  | Some(toplevel) ->
  Hashtbl.remove state.toplevels i;
  Rocq_toplevel.stop toplevel

let fork state i =
  match Hashtbl.find_opt state.toplevels i with
  | None           -> notify "Error: no toplevel %i." i
  | Some(toplevel) ->
  match Rocq_toplevel.fork toplevel with
  | Error(s) -> notify "Error: %s." s
  | Ok(t)    ->
  let id = state.next in
  state.next <- id + 1;
  Hashtbl.add state.toplevels id t;
  notify "New toplevel forked with identifier %i." id

let handle_command state line =
  try
    if String.starts_with ~prefix:"run " line then
      Scanf.sscanf line "run %i %S" (run state.cur_toplevel)
    else if String.starts_with ~prefix:"back_to " line then
      Scanf.sscanf line "back_to %i" (back_to state.cur_toplevel)
    else if String.starts_with ~prefix:"switch " line then
      Scanf.sscanf line "switch %i" (switch state)
    else if String.starts_with ~prefix:"stop " line then
      Scanf.sscanf line "stop %i" (stop state)
    else if String.starts_with ~prefix:"fork" line then
      Scanf.sscanf line "fork %i" (fork state)
    else
      notify "Error: invalid query."
  with Scanf.Scan_failure(_) | Failure(_) | End_of_file ->
    notify "Error: ill-formed query."

let _ =
  let state =
    let cur_toplevel =
      let args = List.tl (Array.to_list Sys.argv) in
      try Rocq_toplevel.init ~args with
      | Failure(s) -> notify "Error: %s." s; exit 1
    in
    let toplevels = Hashtbl.create 13 in
    Hashtbl.add toplevels 0 cur_toplevel;
    {toplevels; next = 1; cur_index = 0; cur_toplevel}
  in
  let rec loop () =
    let sid = Rocq_toplevel.StateID.current state.cur_toplevel in
    let sid = Rocq_toplevel.StateID.to_int state.cur_toplevel sid in
    Printf.printf "[%i] %i > %!" state.cur_index sid;
    match In_channel.input_line stdin with
    | None -> Printf.printf "[EOF]\n"
    | Some(line) ->
    Printf.printf "%s\n%!" line;
    handle_command state line;
    loop ()
  in
  loop ();
  Hashtbl.iter (fun _ toplevel -> Rocq_toplevel.stop toplevel) state.toplevels

let output_json oc json =
  Yojson.Safe.pretty_to_channel ~std:true oc json

let run toplevel off text =
  match Rocq_toplevel.run toplevel ~off ~text with
  | Ok(data) ->
      let json = Rocq_toplevel.run_data_to_yojson data in
      Printf.printf "%a\nOK\n%!" output_json json
  | Error(s, data) ->
      let json = Rocq_toplevel.run_error_to_yojson data in
      Printf.printf "%a\nError: %s\n%!" output_json json s

let back_to toplevel sid =
  let sid = Rocq_toplevel.StateID.unsafe_of_int toplevel sid in
  match Rocq_toplevel.back_to toplevel ~sid with
  | Ok(()) -> Printf.printf "OK\n%!"
  | Error(s) -> Printf.printf "Error: %s\n%!" s

let handle_command toplevel line =
  try
    if String.starts_with ~prefix:"run " line then
      Scanf.sscanf line "run %i %S" (run toplevel)
    else if String.starts_with ~prefix:"back_to " line then
      Scanf.sscanf line "back_to %i" (back_to toplevel)
    else
      Printf.printf "Error: invalid query."
  with Scanf.Scan_failure(_) | Failure(_) | End_of_file ->
    Printf.printf "Error: ill-formed query."

let _ =
  let toplevel =
    let args = List.tl (Array.to_list Sys.argv) in
    Rocq_toplevel.init ~args
  in
  let rec loop () =
    if In_channel.isatty stdin then begin
      let sid = Rocq_toplevel.StateID.(to_int toplevel (current toplevel)) in
      Printf.printf "%i > %!" sid;
    end;
    match In_channel.input_line stdin with
    | None -> ()
    | Some(line) -> handle_command toplevel line; loop ()
  in
  loop ();
  Rocq_toplevel.stop toplevel

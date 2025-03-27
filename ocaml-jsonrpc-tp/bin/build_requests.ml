let output_packet i m params =
  match params with
  | None         ->
      Printf.printf {|{"jsonrpc":"2.0","method":"%s","id":%i}|} m i;
      Printf.printf "\n%!"
  | Some(params) ->
      Printf.printf {|{"jsonrpc":"2.0","method":"%s","id":%i,"params":%s}|}
        m i params;
      Printf.printf "\n%!"

let rec process_lines i =
  match In_channel.input_line stdin with None -> () | Some(line) ->
  let (m, params) =
    match String.index_opt line ' ' with
    | None    -> (line, None)
    | Some(i) ->
        let m = String.sub line 0 i in
        let params = String.sub line (i+1) (String.length line - i - 1) in
        (m, Some(params))
  in
  output_packet i m params;
  process_lines (i+1)

let _ = process_lines 1

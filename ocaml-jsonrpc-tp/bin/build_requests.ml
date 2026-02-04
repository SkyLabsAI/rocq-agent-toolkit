let output_packet id m params =
  match (id, params) with
  | (None   , None        ) ->
      Printf.printf {|{"jsonrpc":"2.0","method":"%s"}|} m;
      Printf.printf "\n%!"
  | (Some(i), None        ) ->
      Printf.printf {|{"jsonrpc":"2.0","method":"%s","id":%i}|} m i;
      Printf.printf "\n%!"
  | (None   , Some(params)) ->
      Printf.printf {|{"jsonrpc":"2.0","method":"%s","params":%s}|} m params;
      Printf.printf "\n%!"
  | (Some(i), Some(params)) ->
      Printf.printf {|{"jsonrpc":"2.0","method":"%s","id":%i,"params":%s}|}
        m i params;
      Printf.printf "\n%!"

let rec process_lines i =
  match In_channel.input_line stdin with None -> () | Some(line) ->
  match String.trim line with "" -> process_lines i | line ->
  let (m, params) =
    match String.index_opt line ' ' with
    | None    -> (line, None)
    | Some(i) ->
        let m = String.sub line 0 i in
        let params = String.sub line (i+1) (String.length line - i - 1) in
        (m, Some(params))
  in
  let (i, id) =
    if m <> "" && m.[0] = '!' then (i, None) else (i+1, Some(i))
  in
  output_packet id m params;
  process_lines i

let _ = process_lines 1

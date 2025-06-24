let output_packet data =
  let len = String.length data + 1 in 
  Printf.printf "Content-Length: %i\r\n\r\n%s\n%!" len data

let rec process_lines () =
  match In_channel.input_line stdin with None -> () | Some(line) ->
  output_packet line;
  process_lines ()

let _ = process_lines ()

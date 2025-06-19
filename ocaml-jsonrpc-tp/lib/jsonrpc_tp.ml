module JSON = Yojson.Safe
module Packet = Jsonrpc.Packet

let send_json ?(oc=stdout) json =
  let data = JSON.to_string ~std:true json in
  let len = String.length data + 1 in
  Printf.fprintf oc "Content-Length: %i\r\n\r\n%s\n%!" len data

let recv_json ?(ic=stdin) () =
  match In_channel.input_line ic with
  | None       -> Ok(None)
  | Some(line) ->
  let len =
    try Scanf.sscanf line "Content-Length: %i\r" (fun i -> Some(i))
    with Scanf.Scan_failure(_) | Failure(_) | End_of_file -> None
  in
  match len with
  | None      ->
      Error(Printf.sprintf "ill-formed package header %S" line)
  | Some(len) ->
  match In_channel.input_line ic with
  | None       -> Error("end of file reached before header end")
  | Some(line) ->
  if line <> "\r" then
    Error(Printf.sprintf "ill-formed package header separator %S" line)
  else
  let data = Bytes.create len in
  try
    for i = 0 to len - 1 do
      Bytes.set data i (input_char ic)
    done;
    let data = Bytes.unsafe_to_string data in
    let json = JSON.from_string data in
    Ok(Some(json))
  with
  | Yojson.Json_error(s) -> Error("JSON parse error.\n" ^ s)
  | End_of_file          -> Error("end of file reached before packet end")

type packet = Jsonrpc.Packet.t

let send ?oc p =
  send_json ?oc (Packet.yojson_of_t p)

let recv ?ic () =
  match recv_json ?ic () with
  | Error(s)       -> Error(s)
  | Ok(None)       -> Ok(None)
  | Ok(Some(json)) ->
  try Ok(Some(Packet.t_of_yojson json)) with Jsonrpc.Json.Of_json(_) ->
    Error("ill-formed JSON-CPC 2.0 packet")

module JSON = Yojson.Safe
module Packet = Jsonrpc.Packet

type t = Jsonrpc.Packet.t

let recv : Eio.Buf_read.t -> (t option, string) result = fun b ->
  let parse_packet =
    let open Eio.Buf_read in
    let open Syntax in
    let length =
      let is_digit c = match c with '0'..'9' -> true | _ -> false in
      let+ s = take_while is_digit in
      int_of_string s
    in
    let* n = string "Content-Length: " *> length <* string "\r\n\r\n" in
    take n
  in
  try Ok(Some(Packet.t_of_yojson (JSON.from_string (parse_packet b)))) with
  | End_of_file -> Ok(None)
  | Failure(s) -> Error(s)
  | Eio.Buf_read.Buffer_limit_exceeded -> Error("buffer limit exceeded")
  | Yojson.Json_error(s) -> Error("JSON parse error.\n" ^ s)
  | Jsonrpc.Json.Of_json(_) -> Error("ill-formed JSON-RPC 2.0 packet")

let send : Eio.Buf_write.t -> t -> unit = fun b packet ->
  let json = Packet.yojson_of_t packet in
  let data = JSON.to_string ~std:true json in
  let len = String.length data + 1 in
  Eio.Buf_write.printf b "Content-Length %i\r\n\r\n%s\n%!" len data

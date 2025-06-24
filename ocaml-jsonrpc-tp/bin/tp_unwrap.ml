let output_packet p =
  let json = Jsonrpc.Packet.yojson_of_t p in
  Printf.printf "%a\n%!" (Yojson.Safe.pretty_to_channel ~std:true) json

let rec process_packets () =
  match Jsonrpc_tp.recv () with
  | Ok(None   ) -> ()
  | Ok(Some(p)) -> output_packet p; process_packets ()
  | Error(e)    -> failwith e

let _ = process_packets ()

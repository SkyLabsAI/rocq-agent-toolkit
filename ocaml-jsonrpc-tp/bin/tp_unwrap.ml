let output_packet p =
  let json = Jsonrpc.Packet.yojson_of_t p in
  Yojson.Safe.to_channel ~std:true stdout json;
  Printf.printf "\n%!"

let rec process_packets () =
  match Jsonrpc_tp.recv () with
  | Ok(None   ) -> ()
  | Ok(Some(p)) -> output_packet p; process_packets ()
  | Error(e)    -> failwith e

let _ = process_packets ()

open Jsonrpc_tp

let handle_request ~name ~params ~notify =
  let (n, payload) =
    match (name, params) with
    | ("echo", Some(`List([`Int(n); payload]))) -> (n, payload)
    | ("echo", _                              ) -> assert false
    | (_     , _                              ) -> assert false
  in
  Unix.sleep n;
  notify ~name:"done_sleeping" ~params:None;
  Service.Response.ok payload

let handle_notification ~name:_ ~params:_ ~notify:_ = ()

let main ~workers ~ic ~oc =
  match Service.run ~ic ~oc ~workers ~handle_request ~handle_notification with
  | Ok(()) -> ()
  | Error(_) -> assert false

let _ =
  let workers =
    match Sys.argv with
    | [|_|]    -> 1
    | [|_; n|] -> int_of_string n
    | _        -> assert false
  in
  main ~workers ~ic:stdin ~oc:stdout

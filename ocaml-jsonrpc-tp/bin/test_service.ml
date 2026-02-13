open Jsonrpc_tp

let handle_request ~name ~params ~notify =
  let task =
    match (name, params) with
    | ("echo", Some(`List([`Int(n); payload]))) -> `Echo(n, payload)
    | ("echo", _                              ) -> assert false
    | ("yes" , Some(`List([`Int(n)])         )) -> `Yes(n)
    | ("yes" , _                              ) -> assert false
    | (_     , _                              ) -> assert false
  in
  let payload =
    match task with
    | `Echo(n, payload) ->
        Unix.sleep n;
        notify ~name:"done_sleeping" ~params:None;
        payload
    | `Yes(n)           ->
        if n > 1000 then notify ~name:"big_string" ~params:None;
        `String(String.make n 'y')
  in
  Service.Response.ok payload

let handle_notification ~name:_ ~params:_ ~notify:_ = ()

let main ~workers ~ic ~oc =
  let run =
    match workers with
    | None          -> Service.run_seq
    | Some(workers) -> Service.run ~workers
  in
  match run ~ic ~oc ~handle_request ~handle_notification with
  | Ok(())   -> ()
  | Error(_) -> assert false

let _ =
  let workers =
    match Sys.argv with
    | [|_|]    -> None
    | [|_; n|] -> Some(int_of_string n)
    | _        -> assert false
  in
  main ~workers ~ic:stdin ~oc:stdout

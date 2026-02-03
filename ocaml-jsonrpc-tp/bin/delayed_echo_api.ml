module API = Jsonrpc_tp.API
module A = API.Args
module S = API.Schema

let api : unit API.api = API.create ~name:"DelayedEcho"

let done_sleeping : unit -> API.notification =
  API.declare_emittable_notification api ~name:"done_sleeping" ?descr:None ~args:A.nil

let _ =
  let args =
    A.add ~name:"seconds" S.int @@
    A.add ~name:"message" S.string @@
    A.nil
  in
  API.declare api ~name:"echo" ~args ~ret:S.string @@
    fun notify () (seconds, (message, ())) ->
  Unix.sleep seconds;
  notify (done_sleeping ());
  message

let main ~workers ~ic ~oc =
  match API.run api ~ic ~oc ~workers () with
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

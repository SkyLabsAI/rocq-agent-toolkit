module API = Jsonrpc_tp.API
module A = API.Args
module S = API.Schema

let api : unit API.api = API.create ~name:"Test"

let done_sleeping : unit -> API.notification =
  API.declare_emittable_notification api ~name:"done_sleeping"
    ?descr:None ~args:A.nil

let big_string : unit -> API.notification =
  API.declare_emittable_notification api ~name:"big_string"
    ?descr:None ~args:A.nil

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

let _ =
  let args =
    A.add ~name:"count" S.int @@
    A.nil
  in
  API.declare api ~name:"yes" ~args ~ret:S.string @@
    fun notify () (count, ()) ->
  if count > 1000 then notify (big_string ());
  String.make count 'y'

let main ~workers ~ic ~oc =
  let run =
    match workers with
    | None          -> API.run_seq
    | Some(workers) -> API.run ~workers
  in
  match run api ~ic ~oc () with
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

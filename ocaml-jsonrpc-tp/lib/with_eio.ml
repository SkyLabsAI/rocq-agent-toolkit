open Eio.Std

module JSON = Yojson.Safe

type handler =
  string ->
  Jsonrpc.Structured.t option ->
  (JSON.t, Jsonrpc.Response.Error.t) Result.t

let main : nb_workers:int -> handler -> unit = fun ~nb_workers handler ->
  Eio_main.run @@ fun env ->
  let requests : Jsonrpc.Request.t option Eio.Stream.t =
    Eio.Stream.create max_int
  in
  let responses : Jsonrpc.Response.t Eio.Stream.t =
    Eio.Stream.create max_int
  in
  (* Function run by each workers. *)
  let rec worker_loop : unit -> unit = fun () ->
    match Eio.Stream.take requests with None -> () | Some(r) ->
    let Jsonrpc.Request.{id; method_; params} = r in
    let result = handler method_ params in
    Eio.Stream.add responses Jsonrpc.Response.{id; result};
    worker_loop ()
  in
  (* Starting the workers. *)
  let domain_mgr = Eio.Stdenv.domain_mgr env in
  let run_worker () = Eio.Domain_manager.run domain_mgr worker_loop in
  Fiber.all (List.init nb_workers (fun _ -> run_worker));
  (* Handle the IO in the main fiber/domain. *)
  let ib = Eio.Buf_read.of_flow ~max_size:1000000 (Eio.Stdenv.stdin env) in
  Eio.Buf_write.with_flow (Eio.Stdenv.stdout env) @@ fun ob ->
  let handle_requests () =
    assert false
  in
  let rec handle_responses () =
    let _ =
      match Eio.Stream.take_nonblocking responses with
      | None -> Fiber.yield ()
      | Some(r) -> Packet.send ob (Jsonrpc.Packet.Response(r))
    in
    handle_responses ()
  in
  Fiber.both handle_requests handle_responses;
  ignore ib

(*
let rec loop in_buf stdout =
  try
    let line = Eio.Buf_read.line in_buf in
    traceln "%s" line;
    Eio.Flow.copy_string (Format.sprintf "Read line: %s\n" line) stdout;
    loop in_buf stdout
  with End_of_file -> ()

let _ =

  let stdout = Eio.Stdenv.stdout env in
  let in_buf = Eio.Buf_read.of_flow ~max_size:1000000 stdin in
  loop in_buf stdout
*)

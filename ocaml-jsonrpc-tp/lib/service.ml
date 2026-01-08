module JSON = Yojson.Safe

type handler =
  method_:string ->
  params:Jsonrpc.Structured.t option ->
  (JSON.t, Jsonrpc.Response.Error.t) Result.t

type state = {
  request_channel : In_channel.t;
  request_queue : Jsonrpc.Request.t Queue.t;
  request_mutex : Mutex.t;
  request_cond : Condition.t;
  response_channel : Out_channel.t;
  response_queue : Jsonrpc.Response.t Queue.t;
  response_mutex : Mutex.t;
  response_cond : Condition.t;
  stopped : bool Atomic.t;
  workers : int Atomic.t;
}

let worker_loop : state -> handler -> unit = fun s handler ->
  let rec loop () =
    Mutex.lock s.request_mutex;
    while Queue.is_empty s.request_queue && not (Atomic.get s.stopped) do
      Condition.wait s.request_cond s.request_mutex
    done;
    let request = Queue.take_opt s.request_queue in
    Mutex.unlock s.request_mutex;
    match request with
    | None ->
        (* No request, we have been stopped. *)
        Atomic.decr s.workers;
        if Atomic.get s.workers = 0 then begin
          Mutex.lock s.response_mutex;
          Condition.broadcast s.response_cond;
          Mutex.unlock s.response_mutex
        end
    | Some(Jsonrpc.Request.{id; method_; params}) ->
        (* Handle the request. *)
        let result = handler ~method_ ~params in
        let response = Jsonrpc.Response.{id; result} in
        Mutex.lock s.response_mutex;
        while Queue.is_empty s.response_queue do
          Condition.wait s.response_cond s.response_mutex
        done;
        let was_empty = Queue.is_empty s.response_queue in
        Queue.add response s.response_queue;
        if was_empty then Condition.broadcast s.response_cond;
        Mutex.unlock s.response_mutex;
        loop ()
  in
  loop ()

let request_loop : state -> unit = fun s ->
  let rec loop () =
    match Base.recv ~ic:s.request_channel () with
    | Ok(None) ->
        Atomic.set s.stopped true;
        Condition.broadcast s.request_cond
    | Ok(Some(Jsonrpc.Packet.Request(r))) ->
        Mutex.lock s.request_mutex;
        let was_empty = Queue.is_empty s.request_queue in
        Queue.add r s.request_queue;
        if was_empty then Condition.broadcast s.request_cond;
        Mutex.unlock s.request_mutex;
        loop ()
    | Ok(Some(_)) ->
        assert false
    | Error(_) ->
        assert false
  in
  loop ()

let response_loop : state -> unit = fun s ->
  let rec loop () =
    Mutex.lock s.response_mutex;
    while Queue.is_empty s.response_queue && Atomic.get s.workers > 0 do
      Condition.wait s.response_cond s.response_mutex
    done;
    let response = Queue.take_opt s.response_queue in
    Mutex.unlock s.response_mutex;
    (* If no request, all workers must have been stopped already. *)
    match response with None -> () | Some(r) ->
    (* Send the response. *)
    Base.send ~oc:s.response_channel (Jsonrpc.Packet.Response(r));
    loop ()
  in
  loop ()

let run : ic:In_channel.t -> oc:Out_channel.t -> workers:int ->
    handler -> unit = fun ~ic ~oc ~workers handler ->
  let state =
    let request_channel = ic in
    let request_queue = Queue.create () in
    let request_mutex = Mutex.create () in
    let request_cond = Condition.create () in
    let response_channel = oc in
    let response_queue = Queue.create () in
    let response_mutex = Mutex.create () in
    let response_cond = Condition.create () in
    let stopped = Atomic.make false in
    let workers = Atomic.make workers in
    {request_channel; request_queue; request_mutex; request_cond;
     response_channel; response_queue; response_mutex; response_cond;
     stopped; workers}
  in
  let workers =
    List.init workers @@ fun _ ->
    Domain.spawn @@ fun _ -> worker_loop state handler
  in
  let responder =
    Domain.spawn @@ fun _ ->
    response_loop state
  in
  request_loop state;
  List.iter Domain.join workers;
  Domain.join responder

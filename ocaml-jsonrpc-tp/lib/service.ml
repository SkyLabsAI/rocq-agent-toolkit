type json = Yojson.Safe.t

type params = [ `Assoc of (string * json) list | `List of json list ] option

module Response = struct
  type t = (json, Jsonrpc.Response.Error.t) Result.t

  type error_code = Jsonrpc.Response.Error.Code.t =
    | ParseError
    | InvalidRequest
    | MethodNotFound
    | InvalidParams
    | InternalError
    | ServerErrorStart
    | ServerErrorEnd
    | ServerNotInitialized
    | UnknownErrorCode
    | RequestFailed
    | ServerCancelled
    | ContentModified
    | RequestCancelled
    | Other of int

  let ok data = Ok(data)

  let error ?(code=RequestFailed) ?data message =
    Error(Jsonrpc.Response.Error.make ?data ~code ~message ())
end

type 'a handler =
  name:string ->
  params:params ->
  notify:(name:string -> params:params -> unit) ->
  'a

type request_handler = Response.t handler

type notification_handler = unit handler

type batch_data = {
  missing : int Atomic.t;
  index : int Atomic.t;
  responses : Jsonrpc.Response.t array;
}

type request_or_notification =
  | Request of Jsonrpc.Request.t * batch_data option
  | Notification of Jsonrpc.Notification.t

let dummy_response = Jsonrpc.Response.ok (`Int(0)) `Null

type state = {
  i_channel : In_channel.t;
  i_queue : request_or_notification Queue.t;
  i_mutex : Mutex.t;
  i_cond : Condition.t;
  o_channel : Out_channel.t;
  o_queue : Jsonrpc.Packet.t Queue.t;
  o_mutex : Mutex.t;
  o_cond : Condition.t;
  stopped : bool Atomic.t;
  workers : int Atomic.t;
  handle_request : request_handler;
  handle_notification : notification_handler;
}

let worker_loop : state -> unit = fun s ->
  let send_packet p =
    Mutex.lock s.o_mutex;
    let was_empty = Queue.is_empty s.o_queue in
    Queue.add p s.o_queue;
    if was_empty then Condition.broadcast s.o_cond;
    Mutex.unlock s.o_mutex
  in
  let notify ~name ~params =
    let n = Jsonrpc.Notification.create ~method_:name ?params () in
    send_packet (Jsonrpc.Packet.Notification(n))
  in
  let rec loop () =
    Mutex.lock s.i_mutex;
    while Queue.is_empty s.i_queue && not (Atomic.get s.stopped) do
      Condition.wait s.i_cond s.i_mutex
    done;
    let p = Queue.take_opt s.i_queue in
    Mutex.unlock s.i_mutex;
    match p with
    | None ->
        (* No request, we have been stopped. *)
        Mutex.lock s.o_mutex;
        if Atomic.fetch_and_add s.workers (-1) = 1 then
          Condition.broadcast s.o_cond;
        Mutex.unlock s.o_mutex
    | Some(Notification(Jsonrpc.Notification.{method_=name; params})) ->
        s.handle_notification ~name ~params ~notify;
        loop ()
    | Some(Request(Jsonrpc.Request.{id; method_=name; params}, bd)) ->
        let result = s.handle_request ~name ~params ~notify in
        let response = Jsonrpc.Response.{id; result} in
        let _ =
          match bd with
          | None -> send_packet (Jsonrpc.Packet.Response(response));
          | Some(bd) ->
          let index = Atomic.fetch_and_add bd.index 1 in
          bd.responses.(index) <- response;
          if Atomic.fetch_and_add bd.missing (-1) = 1 then begin
            let responses = Array.to_list bd.responses in
            send_packet (Jsonrpc.Packet.Batch_response(responses))
          end
        in
        loop ()
  in
  loop ()

let request_loop : state -> (unit, string) Result.t = fun s ->
  let enqueue request_or_notification =
    Mutex.lock s.i_mutex;
    let was_empty = Queue.is_empty s.i_queue in
    Queue.add request_or_notification s.i_queue;
    if was_empty then Condition.broadcast s.i_cond;
    Mutex.unlock s.i_mutex
  in
  let enqueue_batch ps =
    Mutex.lock s.i_mutex;
    let was_empty = Queue.is_empty s.i_queue in
    List.iter (fun p -> Queue.add p s.i_queue) ps;
    if was_empty then Condition.broadcast s.i_cond;
    Mutex.unlock s.i_mutex
  in
  let rec loop () =
    match Base.recv ~ic:s.i_channel () with
    | Ok(None) ->
        Ok(())
    | Ok(Some(Jsonrpc.Packet.Request(r))) ->
        enqueue (Request(r, None));
        loop ()
    | Ok(Some(Jsonrpc.Packet.Batch_call(ps))) ->
        let nb_requests =
          let f n p = match p with `Request(_) -> n + 1 | _ -> n in
          List.fold_left f 0 ps
        in
        let bd =
          Lazy.from_fun @@ fun _ ->
          let missing = Atomic.make nb_requests in
          let index = Atomic.make 0 in
          let responses = Array.make nb_requests dummy_response in
          {missing; index; responses}
        in
        let make p =
          match p with
          | `Request(r) -> Request(r, Some(Lazy.force bd))
          | `Notification(n) -> Notification(n)
        in
        enqueue_batch (List.map make ps);
        loop ()
    | Ok(Some(Jsonrpc.Packet.Notification(n))) ->
        enqueue (Notification(n));
        loop ()
    | Ok(Some(Jsonrpc.Packet.Response(_))) ->
        Error("Unexpected response received.")
    | Ok(Some(Jsonrpc.Packet.Batch_response(_))) ->
        Error("Unexpected batch response received.")
    | Error(s) ->
        Error("Invalid packet received: " ^ s ^ ".")
  in
  loop ()

let response_loop : state -> unit = fun s ->
  let rec loop () =
    Mutex.lock s.o_mutex;
    while Queue.is_empty s.o_queue && Atomic.get s.workers > 0 do
      Condition.wait s.o_cond s.o_mutex
    done;
    let packet = Queue.take_opt s.o_queue in
    Mutex.unlock s.o_mutex;
    (* If no request, all workers must have been stopped already. *)
    match packet with None -> () | Some(packet) ->
    (* Send the response. *)
    Base.send ~oc:s.o_channel packet;
    loop ()
  in
  loop ()

let run : ic:In_channel.t -> oc:Out_channel.t -> workers:int ->
    handle_request:request_handler ->
    handle_notification:notification_handler -> (unit, string) Result.t =
    fun ~ic ~oc ~workers ~handle_request ~handle_notification ->
  let state =
    let i_channel = ic in
    let i_queue = Queue.create () in
    let i_mutex = Mutex.create () in
    let i_cond = Condition.create () in
    let o_channel = oc in
    let o_queue = Queue.create () in
    let o_mutex = Mutex.create () in
    let o_cond = Condition.create () in
    let stopped = Atomic.make false in
    let workers = Atomic.make workers in
    {i_channel; i_queue; i_mutex; i_cond;
     o_channel; o_queue; o_mutex; o_cond;
     stopped; workers; handle_request; handle_notification}
  in
  let workers =
    List.init workers @@ fun _ ->
    Domain.spawn @@ fun _ ->
    worker_loop state
  in
  let responder =
    Domain.spawn @@ fun _ ->
    response_loop state
  in
  let status = request_loop state in
  Atomic.set state.stopped true;
  Condition.broadcast state.i_cond;
  List.iter Domain.join workers;
  Domain.join responder;
  status

let run_seq : ic:In_channel.t -> oc:Out_channel.t ->
    handle_request:request_handler ->
    handle_notification:notification_handler -> (unit, string) Result.t =
    fun ~ic ~oc ~handle_request ~handle_notification ->
  let notify ~name ~params =
    let n = Jsonrpc.Notification.create ~method_:name ?params () in
    Base.send ~oc (Jsonrpc.Packet.Notification(n))
  in
  let notify_ignored ~name:_ ~params:_ = () in
  let rec loop () =
    match Base.recv ~ic () with
    | Ok(None) ->
        Ok(())
    | Ok(Some(Jsonrpc.Packet.Request(r))) ->
        let Jsonrpc.Request.{id; method_=name; params} = r in
        let result = handle_request ~name ~params ~notify in
        let response = Jsonrpc.Response.{id; result} in
        Base.send ~oc (Jsonrpc.Packet.Response(response));
        loop ()
    | Ok(Some(Jsonrpc.Packet.Batch_call(ps))) ->
        let handle rs p =
          match p with
          | `Request(r)      ->
              let Jsonrpc.Request.{id; method_=name; params} = r in
              let result = handle_request ~name ~params ~notify in
              let response = Jsonrpc.Response.{id; result} in
              response :: rs
          | `Notification(n) ->
              let Jsonrpc.Notification.{method_=name; params} = n in
              handle_notification ~name ~params ~notify:notify_ignored;
              rs
        in
        let rs = List.fold_left handle [] ps in
        if rs <> [] then Base.send ~oc (Jsonrpc.Packet.Batch_response(rs));
        loop ()
    | Ok(Some(Jsonrpc.Packet.Notification(n))) ->
        let Jsonrpc.Notification.{method_=name; params} = n in
        handle_notification ~name ~params ~notify:notify_ignored;
        loop ()
    | Ok(Some(Jsonrpc.Packet.Response(_))) ->
        Error("Unexpected response received.")
    | Ok(Some(Jsonrpc.Packet.Batch_response(_))) ->
        Error("Unexpected batch response received.")
    | Error(s) ->
        Error("Invalid packet received: " ^ s ^ ".")
  in
  loop ()

(** JSON-RCP Transport Protocol

    A packet must be of the form: "Content-Length: <size>\r\n\r\n<data>" where
    the data part is a JSON string complying to the JSON-RPC 2.0 protocol. The
    size part must correspond to the length of the JSON string in bytes. *)

(** Type of a JSON-RCP 2.0 packet (provided by the [jsonrpc] package). *)
type packet = Jsonrpc.Packet.t

(** [send ?oc p] sends the JSON-RCP packet [p] on channel [oc], or [stdout] by
    default. The data is sent using the above-described protocol. *)
val send : ?oc:Out_channel.t -> packet -> unit

(** [recv ?ic ()] attempts to receive a JSON-RCP packet on channel [ic], or on
    [stdin] by default. The value [Ok(None)] is returned if the end of file is
    reached. The value [Ok(Some(p))] is returned when a well-formed packet [p]
    is received. The value [Error(s)] is returned with an error message [s] if
    the received data does not conform to the above-described protocol. *)
val recv : ?ic:In_channel.t -> unit -> (packet option, string) result

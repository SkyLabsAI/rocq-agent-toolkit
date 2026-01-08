(** JSON-RCP Transport Protocol

    A packet must be of the form: "Content-Length: <size>\r\n\r\n<data>" where
    the data part is a JSON string complying to the JSON-RPC 2.0 protocol. The
    size part must correspond to the length of the JSON string in bytes. *)

(** Type of a JSON-RCP 2.0 packet (provided by the [jsonrpc] package). *)
type t = Jsonrpc.Packet.t

(** [send buf p] sends the JSON-RCP packet [p] on write buffer [buf]. The data
    is sent using the above-described protocol. *)
val send : Eio.Buf_write.t -> t -> unit

(** [recv buf] attempts to read a JSON-RCP packet on the read buffer [buf]. If
    a well-formed packet [p] is read, the value [Ok(Some(p))] is returned. The
    value [Ok(None)] is returned if the end of file is immediately reached. An
    [Error(s)] value is returned, with an error message [s], when the received
    data does not conform to the above-described protocol. *)
val recv : Eio.Buf_read.t -> (t option, string) result


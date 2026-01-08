module JSON = Yojson.Safe

type handler =
  method_:string ->
  params:Jsonrpc.Structured.t option ->
  (JSON.t, Jsonrpc.Response.Error.t) Result.t

val run :
  ic:In_channel.t ->
  oc:Out_channel.t ->
  workers:int ->
  handler ->
  unit

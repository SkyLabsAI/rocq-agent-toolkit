(** Formatter with continuation. *)
type ('a, 'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

(** [panic fmt ...] interrupts the program with [exit 1], after displaying the
    error message specified by [fmt] (and subsequent arguments) to [stderr]. A
    newline character is added to the message, and [stderr] is flushed. *)
let panic : ('a,'b) koutfmt -> 'a = fun fmt ->
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter (fmt ^^ "\n%!")

let loc_to_yojson loc =
  match loc with
  | None -> `Null
  | Some(loc) -> Rocq_loc.to_yojson loc

let main : Document.t -> unit = fun state ->
  let json =
    match Document.load_file state with
    | Ok(())       -> None
    | Error(s,loc) ->
        let fields =
          ("status" , `String("error")) ::
          ("message", `String(s)) ::
          ("loc"    , loc_to_yojson loc) :: []
        in
        Some(`Assoc(fields))
  in
  let prev_data = ref None in
  let rec loop () =
    match Document.suffix state with
    | [] -> `Assoc([("status", `String("success"))])
    | _  ->
    match Document.run_step state with
    | Error(s,err) ->
        let loc =
          match err with
          | None -> None
          | Some(err) -> err.Rocq_toplevel.error_loc
        in
        let fields =
          ("status" , `String("error")) ::
          ("message", `String(s)) ::
          ("loc"    , loc_to_yojson loc) :: []
        in
        let fields =
          match !prev_data with
          | None -> fields
          | Some(data) ->
          match data.Rocq_toplevel.proof_state with
          | None -> fields
          | Some(p) ->
          let p = Rocq_toplevel.proof_state_to_yojson p in
          fields @ [("proof_state", p)]
        in
        `Assoc(fields)
    | Ok(None)     -> loop ()
    | Ok(Some(v))  -> prev_data := Some(v); loop ()
  in
  let json =
    match json with
    | Some(json) -> json
    | None       -> loop ()
  in
  let json = Yojson.Safe.pretty_to_string ~std:true json in
  Printf.printf "%s%!" json

(* We assume a single Rocq source file is passed last. *)
let parse_args : argv:string array -> string list * string = fun ~argv ->
  let (argv, rocq_args) = Rocq_args.split ~argv in
  let argc = Array.length argv in
  if argc < 2 then panic "Usage: %s FILE.v [-- ROCQ ARGS]" argv.(0);
  let file = argv.(argc - 1) in
  if not (Filename.check_suffix file ".v") then
    panic "Error: a Rocq source file is expected as last argument.";
  (rocq_args, file)

let _ =
  let (args, file) = parse_args ~argv:Sys.argv in
  try main (Document.init ~args ~file) with
  | Sys_error(s) | Failure(s) -> panic "Error: %s." s

(** Formatter with continuation. *)
type ('a, 'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

(** [panic fmt ...] interrupts the program with [exit 1], after displaying the
    error message specified by [fmt] (and subsequent arguments) to [stderr]. A
    newline character is added to the message, and [stderr] is flushed. *)
let panic : ('a,'b) koutfmt -> 'a = fun fmt ->
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter (fmt ^^ "\n%!")

let main : Document.t -> unit = fun state ->
  let json =
    match Document.load_file state with
    | Ok(())       -> None
    | Error(loc,s) ->
        let fields =
          ("status" , `String("error")) ::
          ("message", `String(s)) ::
          ("loc"    , Document.loc_to_json loc) :: []
        in
        Some(`Assoc(fields))
  in
  let prev_data = ref None in
  let rec loop () =
    match Document.has_suffix state with
    | false -> `Assoc([("status", `String("success"))])
    | true  ->
    match Document.run_step state with
    | Error(loc,s) ->
        let fields =
          ("status" , `String("error")) ::
          ("message", `String(s)) ::
          ("loc"    , Document.loc_to_json loc) :: []
        in
        let fields =
          match !prev_data with
          | None -> fields
          | Some(data) ->
          match data.Document.open_subgoals with
          | None -> fields
          | Some(goals) -> fields @ [("goals", `String(goals))]
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
  let argc = Array.length argv in
  if argc < 2 then panic "Usage: %s [ROCQ ARGS] FILE.v" argv.(0);
  let args =
    let args = ref [] in
    for i = argc - 2 downto 1 do args := argv.(i) :: !args done;
    !args
  in
  let file = argv.(argc - 1) in
  if not (Filename.check_suffix file ".v") then
    panic "Error: a Rocq source file is expected as last argument.";
  (args, file)

let _ =
  let (args, file) = parse_args ~argv:Sys.argv in
  let state = Document.init ~args ~file in
  try main state with
  | Sys_error(s) -> panic "Error: %s" s

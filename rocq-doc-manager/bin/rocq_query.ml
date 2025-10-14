(** Formatter with continuation. *)
type ('a, 'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

(** [panic fmt ...] interrupts the program with [exit 1], after displaying the
    error message specified by [fmt] (and subsequent arguments) to [stderr]. A
    newline character is added to the message, and [stderr] is flushed. *)
let panic : ('a,'b) koutfmt -> 'a = fun fmt ->
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter (fmt ^^ "\n%!")

let main : Document.t -> unit = fun state ->
  let _ =
    match Document.load_file state with
    | Ok(())     -> ()
    | Error(_,s) -> panic "Error: failed to load the file.\n%s" s
  in
  let rec loop () =
    match Document.has_suffix state with
    | false -> ()
    | true  ->
    match Document.run_step state with
    | Ok(_)      -> loop ()
    | Error(_,s) -> panic "Error: failed to process a command.\n%s" s
  in
  loop ();
  let feedback = Document.get_feedback state in
  let feedback = List.filter (fun f -> f.Document.kind = `Notice) feedback in
  match feedback with
  | []          -> panic "Error: the last command gave no feedback."
  | _ :: _ :: _ -> panic "Error: the last command gave too much feedback."
  | [f]         ->
  let feedback = f.Document.text in
  Printf.printf "%s%!" feedback

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
  let state = Document.init ~args ~file in
  try main state with
  | Sys_error(s) -> panic "Error: %s" s

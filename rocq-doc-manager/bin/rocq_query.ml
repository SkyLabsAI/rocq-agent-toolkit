(** Formatter with continuation. *)
type ('a, 'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

(** [panic fmt ...] interrupts the program with [exit 1], after displaying the
    error message specified by [fmt] (and subsequent arguments) to [stderr]. A
    newline character is added to the message, and [stderr] is flushed. *)
let panic : ('a,'b) koutfmt -> 'a = fun fmt ->
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter (fmt ^^ "\n%!")

type input = File | Stdin

let load : input -> Document.t -> unit = fun input state ->
  let load_file () =
    match Document.load_file state with
    | Ok(())     -> ()
    | Error(s,_) -> panic "Error: failed to load the file.\n%s" s
  in
  let load_stdin () =
    let text = In_channel.input_all stdin in
    match snd (Document.replace_suffix state ~text) with
    | Ok(())     -> ()
    | Error(s,_) -> panic "Error: failed to load standard input.\n%s" s
  in
  match input with
  | File  -> load_file ()
  | Stdin -> load_stdin ()

let main : input -> Document.t -> unit = fun input state ->
  load input state;
  let rec loop last_data =
    match Document.suffix state with
    | [] -> last_data
    | _  ->
    match Document.run_step state with
    | Ok(None)   -> loop last_data
    | Ok(data)   -> loop data
    | Error(s,_) -> panic "Error: failed to process a command.\n%s" s
  in
  match loop None with
  | None    -> panic "Error: no command were run."
  | Some(d) ->
  let filter Rocq_toplevel.{level; text; _} =
    match level with
    | Feedback.Notice -> Some(text)
    | _ -> None
  in
  match List.filter_map filter d.Rocq_toplevel.feedback_messages with
  | [] -> panic "Error: the last command gave no notice feedback."
  | ls -> List.iter (Printf.printf "%s%!") ls

let parse_args : argv:string array -> string list * input * string =
    fun ~argv ->
  let (argv, rocq_args) = Rocq_args.split ~argv in
  let usage () =
    panic "Usage: %s [--stdin] FILE.v [-- ROCQ ARGS]" argv.(0)
  in
  let (input, file) =
    match Array.to_list argv with
    | [_; file]            -> (File , file)
    | [_; "--stdin"; file] -> (Stdin, file)
    | _                    -> usage ()
  in
  if not (Filename.check_suffix file ".v") then
    panic "Error: a Rocq source file is expected as last argument.";
  (rocq_args, input, file)

let _ =
  let (args, input, file) = parse_args ~argv:Sys.argv in
  try main input (Document.init ~args ~file) with
  | Sys_error(s) | Failure(s) -> panic "Error: %s." s

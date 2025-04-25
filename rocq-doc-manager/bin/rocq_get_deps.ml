(** Formatter with continuation. *)
type ('a, 'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

(** [panic fmt ...] interrupts the program with [exit 1], after displaying the
    error message specified by [fmt] (and subsequent arguments) to [stderr]. A
    newline character is added to the message, and [stderr] is flushed. *)
let panic : ('a,'b) koutfmt -> 'a = fun fmt ->
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter (fmt ^^ "\n%!")

let or_panic : ('a, string) result -> 'a = fun res ->
  match res with
  | Error(s) -> panic "Error: %s" s
  | Ok(v)    -> v

let main : Document.t -> unit = fun state ->
  let json_items = ref [] in
  or_panic (Document.load_file state);
  begin
    let text = "Require Import skylabs_ai.tools.term_deps.plugin." in
    match Document.insert_command state ~text with
    | Error(_,s) -> panic "Error: %s" s
    | Ok(_)      -> Document.insert_blanks state ~text:"\n"
  end;
  let handle_inductive s =
    let fields = [("name", `String(s)); ("kind", `String("Inductive"))] in
    json_items := `Assoc(fields) :: !json_items
  in
  let handle_constant s =
    let text = "DepsOfJSON " ^ s ^ "." in
    match Document.insert_command state ~text with
    | Error(_,s) -> panic "Error: %s" s
    | Ok(_)      ->
        let open Document in
        let feedback = Document.get_feedback state in
        match List.find_opt (fun f -> f.kind = `Notice) feedback with
        | None    -> assert false
        | Some(f) ->
        json_items := Yojson.Safe.from_string f.text :: !json_items;
        Document.insert_blanks state ~text:"\n"
  in
  let rec loop () =
    match Document.has_suffix state with
    | false -> ()
    | true  ->
    match Document.run_step state with
    | Error(_,s)  -> panic "Error: %s" s
    | Ok(None)    -> loop ()
    | Ok(Some(d)) ->
    List.iter handle_inductive d.Document.new_inductives;
    List.iter handle_constant d.Document.new_constants;
    loop ()
  in
  loop ();
  let json = `List(List.rev !json_items) in
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

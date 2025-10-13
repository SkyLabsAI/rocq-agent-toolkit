(** Formatter with continuation. *)
type ('a, 'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

(** [panic fmt ...] interrupts the program with [exit 1], after displaying the
    error message specified by [fmt] (and subsequent arguments) to [stderr]. A
    newline character is added to the message, and [stderr] is flushed. *)
let panic : ('a,'b) koutfmt -> 'a = fun fmt ->
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter (fmt ^^ "\n%!")

module List = struct
  include List

  let rev_map_filter : ('a -> 'b option) -> 'a list -> 'b list = fun f xs ->
    let rec filter acc xs =
      match xs with
      | []      -> acc
      | x :: xs ->
      match f x with
      | None    -> filter acc xs
      | Some(v) -> filter (v :: acc) xs
    in
    filter [] xs
end

let main : Document.t -> unit = fun state ->
  let json_items = ref [] in
  let _ =
    match Document.load_file state with
    | Ok(())       -> ()
    | Error(loc,e) ->
        let loc =
          match loc with None -> "" | Some(loc) ->
          Pp.string_of_ppcmds Pp.(Loc.pr loc ++ str ":" ++ fnl ())
        in
        panic "%sError: %s" loc e
  in
  let _ =
    let text = "Require Import skylabs_ai.tools.term_deps.plugin." in
    match Document.run_command state ~text with
    | Ok(_)    -> ()
    | Error(e) -> panic "Error: %s" e
  in
  let removed_inductives = Hashtbl.create 11 in
  let handle_removed_inductive loc s =
    Hashtbl.add removed_inductives s loc
  in
  let removed_constants = Hashtbl.create 11 in
  let handle_removed_constant loc s =
    Hashtbl.add removed_constants s loc
  in
  let handle_inductive Document.{off; len} s =
    let json () =
      if Hashtbl.mem removed_inductives s then None else
      Some(`Assoc([
        ("name", `String(s));
        ("kind", `String("Inductive"));
        ("off" , `Int(off));
        ("len" , `Int(len));
      ]))
    in
    json_items := Lazy.from_fun json :: !json_items
  in
  let handle_constant Document.{off; len} s =
    let json () =
      if Hashtbl.mem removed_constants s then None else
      let text = "DepsOfJSON " ^ s ^ "." in
      match Document.insert_command state ~text with
      | Error(_,s) -> panic "Error: %s" s
      | Ok(_)      ->
      let open Document in
      let feedback = Document.get_feedback state in
      match List.find_opt (fun f -> f.kind = `Notice) feedback with
      | None    -> assert false
      | Some(f) ->
      let json =
        let fields =
          match Yojson.Safe.from_string f.text with
          | `Assoc(fields) -> fields
          | _              -> assert false
        in
        `Assoc(fields @ [
          ("off", `Int(off));
          ("len", `Int(len));
        ])
      in
      Document.insert_blanks state ~text:"\n";
      Some(json)
    in
    json_items := Lazy.from_fun json :: !json_items;
  in
  let rec loop () =
    match Document.has_suffix state with
    | false -> ()
    | true  ->
    match Document.run_step state with
    | Error(_,s)  -> panic "Error: %s" s
    | Ok(None)    -> loop ()
    | Ok(Some(d)) ->
    let loc = Option.get (Document.byte_loc_of_last_step state) in
    List.iter (handle_removed_inductive loc) d.Document.removed_inductives;
    List.iter (handle_removed_constant loc) d.Document.removed_constants;
    List.iter (handle_inductive loc) d.Document.new_inductives;
    List.iter (handle_constant loc) d.Document.new_constants;
    loop ()
  in
  loop ();
  let json = `List(List.rev_map_filter Lazy.force !json_items) in
  let json = Yojson.Safe.pretty_to_string ~std:true json in
  Printf.printf "%s%!" json

(* We assume a single Rocq source file is passed last. *)
let parse_args : argv:string array -> string list * string = fun ~argv ->
  let (argv, rocq_args) = Rocq_args.get_args ~argv in
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

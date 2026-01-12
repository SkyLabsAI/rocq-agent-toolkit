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

type byte_loc = {off : int; len : int}

let main : Document.t -> unit = fun state ->
  let json_items = ref [] in
  let _ =
    match Document.load_file state with
    | Ok(())       -> ()
    | Error(e,loc) ->
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
  let handle_removed_inductive loc i =
    let s = Names.MutInd.to_string i in
    Hashtbl.add removed_inductives s loc
  in
  let removed_constants = Hashtbl.create 11 in
  let handle_removed_constant loc c =
    let s = Names.Constant.to_string c in
    Hashtbl.add removed_constants s loc
  in
  let handle_added_inductive {off; len} i =
    let s = Names.MutInd.to_string i in
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
  let handle_added_constant {off; len} c =
    let s = Names.Constant.to_string c in
    let json () =
      if Hashtbl.mem removed_constants s then None else
      let text = "DepsOfJSON " ^ s ^ "." in
      match Document.query_json state ~text with
      | Error(s) -> panic "Error: %s" s
      | Ok(json) ->
      let json =
        let fields =
          match json with
          | `Assoc(fields) -> fields
          | _              -> assert false
        in
        `Assoc(fields @ [
          ("off", `Int(off));
          ("len", `Int(len));
        ])
      in
      Some(json)
    in
    json_items := Lazy.from_fun json :: !json_items;
  in
  let rec loop () =
    match Document.suffix state with
    | [] -> ()
    | _  ->
    match Document.run_step state with
    | Error(s, _) -> panic "Error: %s" s
    | Ok(None)    -> loop ()
    | Ok(Some(d)) ->
    let loc =
      match Document.rev_prefix state with
      | p :: _ -> {off = p.off; len = String.length p.text}
      | []     -> assert false
    in
    let open Rocq_toplevel in
    let diff = d.globrefs_diff in
    List.iter (handle_removed_inductive loc) diff.removed_inductives;
    List.iter (handle_removed_constant loc) diff.removed_constants;
    List.iter (handle_added_inductive loc) diff.added_inductives;
    List.iter (handle_added_constant loc) diff.added_constants;
    loop ()
  in
  loop ();
  let json = `List(List.rev_map_filter Lazy.force !json_items) in
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

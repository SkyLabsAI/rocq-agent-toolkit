(** Formatter with continuation. *)
type ('a, 'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

(** [panic fmt ...] interrupts the program with [exit 1], after displaying the
    error message specified by [fmt] (and subsequent arguments) to [stderr]. A
    newline character is added to the message, and [stderr] is flushed. *)
let panic : ('a,'b) koutfmt -> 'a = fun fmt ->
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter (fmt ^^ "\n%!")

let rset = Jsonrpc_tp_loop.create ()

let add_handler name pspec a =
  Jsonrpc_tp_loop.add rset name pspec a

let located_error ~loc s =
  let loc = Document.loc_to_json loc in
  Error(Some(`Assoc([("loc", loc)])), s)

module P = Jsonrpc_tp_loop.Params

let _ =
  add_handler "load_file" P.nil @@ fun d () ->
  match Document.load_file d with
  | Error(loc, s) -> (d, located_error ~loc s)
  | Ok(())        -> (d, Ok(`Null))

let _ =
  add_handler "insert_blanks" P.(cons string nil) @@ fun d (text, ()) ->
  Document.insert_blanks d ~text;
  (d, Ok(`Null))

let _ =
  add_handler "insert_command" P.(cons string nil) @@ fun d (text, ()) ->
  match Document.insert_command d ~text with
  | Error(loc, s) -> (d, located_error ~loc s)
  | Ok(data)      -> (d, Ok(Document.command_data_to_json data))

let _ =
  add_handler "run_command" P.(cons string nil) @@ fun d (text, ()) ->
  match Document.run_command d ~text with
  | Error(s) -> (d, Error(None, s))
  | Ok(data) -> (d, Ok(Document.command_data_to_json data))

let _ =
  add_handler "cursor_index" P.nil @@ fun d () ->
  let index = Document.cursor_index d in
  (d, Ok(`Int(index)))

let _ =
  add_handler "revert_before" P.(cons bool (cons int nil)) @@
    fun d (erase, (index, ())) ->
  Document.revert_before d ~erase ~index;
  (d, Ok(`Null))

let _ =
  add_handler "advance_to" P.(cons int nil) @@ fun d (index, ()) ->
  match Document.advance_to d ~index with
  | Ok(())        -> (d, Ok(`Null))
  | Error(loc, s) -> (d, located_error ~loc s)

let _ =
  add_handler "go_to" P.(cons int nil) @@ fun d (index, ()) ->
  match Document.advance_to d ~index with
  | Ok(())        -> (d, Ok(`Null))
  | Error(loc, s) -> (d, located_error ~loc s)

let _ =
  add_handler "clear_suffix" P.nil @@ fun d () ->
  Document.clear_suffix d;
  (d, Ok(`Null))

let _ =
  add_handler "run_step" P.nil @@ fun d () ->
  match Document.run_step d with
  | Error(loc, s)  -> (d, located_error ~loc s)
  | Ok(None)       -> (d, Ok(`Null))
  | Ok(Some(data)) -> (d, Ok(Document.command_data_to_json data))

let _ =
  add_handler "doc_prefix" P.nil @@ fun d () ->
  let make ~kind ~off ~text =
    `Assoc([
      ("kind"  , `String(kind));
      ("offset", `Int(off));
      ("text"  , `String(text));
    ])
  in
  let prefix = Document.doc_prefix d make in
  (d, Ok(`List(prefix)))

let _ =
  add_handler "doc_suffix" P.nil @@ fun d () ->
  let make ~kind ~text =
    `Assoc([
      ("kind"  , `String(kind));
      ("text"  , `String(text));
    ])
  in
  let prefix = Document.doc_suffix d make in
  (d, Ok(`List(prefix)))

let _ =
  add_handler "has_suffix" P.nil @@ fun d () ->
  let b = Document.has_suffix d in
  (d, Ok(`Bool(b)))

let _ =
  add_handler "commit" P.(cons bool nil) @@ fun d (include_suffix, ()) ->
  Document.commit ~include_suffix d;
  (d, Ok(`Null))

let _ =
  add_handler "compile" P.nil @@ fun d () ->
  let (ret, out, err) = Document.compile d in
  let json =
    let items = [("stdout", `String(out)); ("stderr", `String(err))] in
    let items =
      match ret with
      | Ok(_)    ->
          ("success", `Bool(true )) :: items
      | Error(s) ->
          ("success", `Bool(false)) :: ("error", `String(s)) :: items
    in
    `Assoc(items)
  in
  (d, Ok(json))

let _ =
  add_handler "get_feedback" P.nil @@ fun d () ->
  let feedback = Document.get_feedback d in
  (d, Ok(`List(List.map Document.feedback_to_json feedback)))

let _ =
  add_handler "text_query" P.(cons string (cons int nil)) @@
  fun d (text, (index, ())) ->
  match Document.text_query d ~text ~index with
  | Error(s) -> (d, Error(None, s))
  | Ok(data) -> (d, Ok(`String(data)))

let _ =
  add_handler "text_query_all" P.(cons string (cons (option (list int)) nil))
  @@ fun d (text, (indices, ())) ->
  match Document.text_query_all d ~text ?indices with
  | Error(s) -> (d, Error(None, s))
  | Ok(data) -> (d, Ok(`List(List.map (fun s -> `String(s)) data)))

let _ =
  add_handler "json_query" P.(cons string (cons int nil)) @@
  fun d (text, (index, ())) ->
  match Document.json_query d ~text ~index with
  | Error(s) -> (d, Error(None, s))
  | Ok(json) -> (d, Ok(json))

let parse_args : argv:string array -> string * string list = fun ~argv ->
  let (argv, rocq_args) = Rocq_args.split ~argv in
  let file =
    match argv with
    | [|_; file|] -> file
    | _           -> panic "Usage: %s FILE.v [-- ROCQ ARGS]" argv.(0)
  in
  if not (Filename.check_suffix file ".v") then
    panic "Error: a Rocq source file was expected as argument.";
  (file, rocq_args)

let _ =
  let (file, args) = parse_args ~argv:Sys.argv in
  let state = Document.init ~args ~file in
  try Jsonrpc_tp_loop.run rset ~ic:stdin ~oc:stdout state with
  | Jsonrpc_tp_loop.Error(s) ->
      Printf.eprintf "%s\n%!" s; exit 1
  | Sys_error(s)             ->
      Printf.eprintf "Error: %s\n%!" s; exit 1

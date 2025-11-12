(** Formatter with continuation. *)
type ('a, 'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

(** [panic fmt ...] interrupts the program with [exit 1], after displaying the
    error message specified by [fmt] (and subsequent arguments) to [stderr]. A
    newline character is added to the message, and [stderr] is flushed. *)
let panic : ('a,'b) koutfmt -> 'a = fun fmt ->
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter (fmt ^^ "\n%!")

module API = Jsonrpc_tp_api
module A = API.Args
module S = API.Schema

let api = API.create ()

let rocq_loc =
  let rocq_source =
    let fields =
      API.Fields.add ~name:"dirpath" S.(nullable string) @@
      API.Fields.add ~name:"file" S.string @@
      API.Fields.nil
    in
    API.declare_object api ~name:"RocqSource"
      ~descr:"Rocq source file information"
      ~encode:Fun.id ~decode:Fun.id fields
  in
  let fields =
    API.Fields.add ~name:"fname"
      ~descr:"source file identification if not run as a toplevel"
      S.(nullable (obj rocq_source)) @@
    API.Fields.add ~name:"line_nb" ~descr:"start line number" S.int @@
    API.Fields.add ~name:"bol_pos"
      ~descr:"position of the beginning of start line" S.int @@
    API.Fields.add ~name:"line_nb_last" ~descr:"end line number" S.int @@
    API.Fields.add ~name:"bol_pos_last"
      ~descr:"position of the beginning of end line" S.int @@
    API.Fields.add ~name:"bp" ~descr:"start position" S.int @@
    API.Fields.add ~name:"ep" ~descr:"end position" S.int @@
    API.Fields.nil
  in
  let encode arg =
    let (fname, (line_nb, (bol_pos, arg))) = arg in
    let (line_nb_last, (bol_pos_last, (bp, (ep, ())))) = arg in
    let fname =
      match fname with
      | None                        -> Rocq_loc.ToplevelInput
      | Some((dirpath, (file, ()))) -> Rocq_loc.InFile({dirpath; file})
    in
    Rocq_loc.{fname; line_nb; bol_pos; line_nb_last; bol_pos_last; bp; ep}
  in
  let decode loc =
    let Rocq_loc.{fname; line_nb; bol_pos; _} = loc in
    let Rocq_loc.{line_nb_last; bol_pos_last; bp; ep; _} = loc in
    let fname =
      match fname with
      | Rocq_loc.ToplevelInput           -> None
      | Rocq_loc.InFile({dirpath; file}) -> Some((dirpath, (file, ())))
    in
    let ret = (line_nb_last, (bol_pos_last, (bp, (ep, ())))) in
    (fname, (line_nb, (bol_pos, ret)))
  in
  API.declare_object api ~name:"RocqLoc"
    ~descr:"Rocq source code location" ~encode ~decode fields

let _ =
  API.declare_full api ~name:"load_file"
    ~descr:"adds the (unprocessed) file contents to the document (note that \
      this requires running sentence-splitting, which requires the input \
      file not to have syntax errors)"
    ~args:A.nil ~ret:S.null ~err:S.(nullable (obj rocq_loc))
    ~err_descr:"optional source code location for the error" @@ fun d () ->
  (d, Document.load_file d)

let _ =
  let args =
    A.add ~name:"text" ~descr:"text of the blanks to insert" S.string @@
    A.nil
  in
  API.declare api ~name:"insert_blanks"
    ~descr:"insert and process blanks at the cursor" ~args ~ret:S.null
    @@ fun d (text, ()) ->
  (d, Document.insert_blanks d ~text)

let command_data =
  let fields =
    API.Fields.add ~name:"open_subgoals"
      ~descr:"open sub-goals, if in a proof" S.(nullable string) @@
    API.Fields.add ~name:"new_constants"
      ~descr:"constants introduced by the command" S.(list string) @@
    API.Fields.add ~name:"removed_constants"
      ~descr:"constants removed by the command" S.(list string) @@
    API.Fields.add ~name:"new_inductives"
      ~descr:"inductives introduced by the command" S.(list string) @@
    API.Fields.add ~name:"removed_inductives"
      ~descr:"inductives removed by the command" S.(list string) @@
    API.Fields.nil
  in
  let encode arg =
    let (open_subgoals, (new_constants, (removed_constants, arg))) = arg in
    let (new_inductives, (removed_inductives, ())) = arg in
    Document.{
      open_subgoals; new_constants; removed_constants;
      new_inductives; removed_inductives
    }
  in
  let decode data =
    let Document.{open_subgoals; _} = data in
    let Document.{new_constants; removed_constants; _} = data in
    let Document.{new_inductives; removed_inductives; _} = data in
    let ret = (new_inductives, (removed_inductives, ())) in
    (open_subgoals, (new_constants, (removed_constants, ret)))
  in
  API.declare_object api ~name:"CommandData"
    ~descr:"data gathered while running a Rocq command" ~encode ~decode fields
 
let text_args =
  A.add ~name:"text" ~descr:"text of the command to insert" S.string A.nil

let _ =
  API.declare_full api ~name:"insert_command"
    ~descr:"insert and process a command at the cursor"
    ~args:text_args ~ret:S.(obj command_data) ~err:S.(nullable (obj rocq_loc))
    ~err_descr:"optional source code location for the error"
    @@ fun d (text, ()) ->
  (d, Document.insert_command d ~text)

let _ =
  API.declare_full api ~name:"run_command"
    ~descr:"process a command at the cursor without inserting it in the \
      document" ~args:text_args ~ret:S.(obj command_data) ~err:S.null
    @@ fun d (text, ()) ->
  (d, Result.map_error (fun s -> ((), s)) (Document.run_command d ~text))

let _ =
  API.declare api ~name:"cursor_index"
    ~descr:"gives the index at the cursor"
    ~args:A.nil ~ret:S.int @@ fun d () ->
  (d, Document.cursor_index d)

let _ =
  let args =
    A.add ~name:"erase" ~descr:"boolean indicating whether reverted items \
      should be erased" S.bool @@
    A.add ~name:"index" ~descr:"index of the item before which the cursor \
      should be revered (one-past-the-end index allowed)" S.int @@
    A.nil
  in
  API.declare api ~name:"revert_before" ~descr:"revert the cursor to an \
    earlier point in the document" ~args ~ret:S.null
    @@ fun d (erase, (index, ())) ->
  (d, Document.revert_before d ~erase ~index)

let index_before_args =
  A.add ~name:"index" ~descr:"integer index before which to move the cursor \
    (one-past-the-end index allowed)" S.int A.nil

let _ =
  API.declare_full api ~name:"advance_to" ~descr:"advance the cursor before \
    the indicated unprocessed item" ~args:index_before_args ~ret:S.null
    ~err:S.(nullable (obj rocq_loc))
    ~err_descr:"optional source code location for the error"
    @@ fun d (index, ()) ->
  (d, Document.advance_to d ~index)

let _ =
  API.declare_full api ~name:"go_to" ~descr:"move the cursor right before \
    the indicated item (whether it is already processed or not)"
    ~args:index_before_args ~ret:S.null ~err:S.(nullable (obj rocq_loc))
    ~err_descr:"optional source code location for the error"
    @@ fun d (index, ()) ->
  (d, Document.go_to d ~index)

let _ =
  API.declare api ~name:"clear_suffix" ~descr:"remove all unprocessed \
    commands from the document" ~args:A.nil ~ret:S.null @@ fun d () ->
  (d, Document.clear_suffix d)

let _ =
  API.declare_full api ~name:"run_step" ~descr:"advance the cursor by \
    stepping over an unprocessed item" ~args:A.nil
    ~ret:S.(nullable (obj command_data))
    ~ret_descr:"data for the command that was run, if any"
    ~err:S.(nullable (obj rocq_loc))
    ~err_descr:"optional source code location for the error" @@ fun d () ->
  (d, Document.run_step d)

let prefix_item =
  let fields =
    API.Fields.add ~name:"kind" S.string @@
    API.Fields.add ~name:"offset" S.int @@
    API.Fields.add ~name:"text" S.string @@
    API.Fields.nil
  in
  API.declare_object api ~name:"PrefixItem"
    ~descr:"document prefix item, appearing before the cursor"
    ~encode:Fun.id ~decode:Fun.id fields

let _ =
  API.declare api ~name:"doc_prefix" ~descr:"gives the list of all processed \
    commands, appearing before the cursor" ~args:A.nil
    ~ret:S.(list (obj prefix_item)) @@ fun d () ->
  let make ~kind ~off ~text = (kind, (off, (text, ()))) in
  (d, Document.doc_prefix d make)

let suffix_item =
  let fields =
    API.Fields.add ~name:"kind" S.string @@
    API.Fields.add ~name:"text" S.string @@
    API.Fields.nil
  in
  API.declare_object api ~name:"SuffixItem"
    ~descr:"document suffix item, appearing after the cursor"
    ~encode:Fun.id ~decode:Fun.id fields

let _ =
  API.declare api ~name:"doc_suffix" ~descr:"gives the list of all \
    unprocessed commands, appearing after the cursor" ~args:A.nil
    ~ret:S.(list (obj suffix_item)) @@ fun d () ->
  let make ~kind ~text = (kind, (text, ())) in
  (d, Document.doc_suffix d make)

let _ =
  API.declare api ~name:"has_suffix" ~descr:"indicates whether the document \
    has a suffix (unprocessed items)" ~args:A.nil ~ret:S.bool @@ fun d () ->
  (d, Document.has_suffix d)

let _ =
  let args =
    A.add ~name:"include_suffix" ~descr:"indicate whether he suffix should \
      be included" S.bool A.nil
  in
  API.declare api ~name:"commit" ~descr:"write the current document contents \
    to the file" ~args ~ret:S.null @@ fun d (include_suffix, ()) ->
  (d, Document.commit ~include_suffix d)

let compile_result =
  let fields =
    API.Fields.add ~name:"success" S.bool @@
    API.Fields.add ~name:"stdout" S.string @@
    API.Fields.add ~name:"stderr" S.string @@
    API.Fields.add ~name:"error" ~descr:"non-null if success is false"
      S.(nullable string) @@
    API.Fields.nil
  in
  let encode (success, (stdout, (stderr, (error, ())))) =
    let ret =
      match (success, error) with
      | (true , None   ) -> Ok(())
      | (true , Some(_)) -> assert false
      | (false, Some(e)) -> Error(e)
      | (false, None   ) -> assert false
    in
    (ret, stdout, stderr)
  in
  let decode (ret, stdout, stderr) =
    match ret with
    | Ok(())       -> (true , (stdout, (stderr, (None, ()))))
    | Error(error) -> (false, (stdout, (stderr, (Some(error), ()))))
  in
  API.declare_object api ~name:"CompileResult"
    ~descr:"result of the `compile` method" ~encode ~decode fields

let _ =
  API.declare api ~name:"compile" ~descr:"compile the current contents of \
    the file with `rocq compile`" ~args:A.nil
    ~ret:S.(obj compile_result) @@ fun d () ->
  (d, Document.compile d)

let _ =
  (* FIXME specify return object precisely. *)
  API.declare api ~name:"get_feedback" ~descr:"gets Rocq's feedback for the \
    last run command (if any)" ~args:A.nil ~ret:S.(list any)
    ~ret_descr:"list of objects with `kind` (array with single string), \
      `text` (string), `loc` (location)" @@ fun d () ->
  let feedback = Document.get_feedback d in
  (d, List.map Document.feedback_to_json feedback)

let query_args =
  A.add ~name:"text" ~descr:"text of the query" S.string @@
  A.add ~name:"index" ~descr:"feedback item index for the result" S.int @@
  A.nil

let _ =
  API.declare_full api ~name:"text_query" ~descr:"runs the given query at \
    the cursor, not updating the state" ~args:query_args ~ret:S.string
    ~ret_descr:"query's result, as taken from the \"info\" \ \"notice\" \
      feedback at the given index" ~err:S.null @@ fun d (text, (index, ())) ->
  let res = Document.text_query d ~text ~index in
  (d, Result.map_error (fun s -> ((), s)) res)

let query_all_args =
  A.add ~name:"text" ~descr:"text of the query" S.string @@
  A.add ~name:"indices" ~descr:"feedback index indices to collect"
    S.(nullable (list int)) @@
  A.nil

let _ =
  API.declare_full api ~name:"text_query_all" ~descr:"runs the given query \
    at the cursor, not updating the state" ~args:query_all_args
    ~ret:S.(list string) ~err:S.null @@ fun d (text, (indices, ())) ->
  let res = Document.text_query_all d ~text ?indices in
  (d, Result.map_error (fun s -> ((), s)) res)

let _ =
  API.declare_full api ~name:"json_query" ~descr:"runs the given query at \
    the cursor, not updating the state" ~args:query_args ~ret:S.any
    ~ret_descr:"arbitrary JSON data, as returned by the query as JSON text, \
    taken from the \"info\" / \"notice\" feedback with the given index"
    ~err:S.null @@ fun d (text, (index, ())) ->
  let res = Document.json_query d ~text ~index in
  (d, Result.map_error (fun s -> ((), s)) res)

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
  match Sys.argv with
  | [|_; "--api-docs"  |] ->
      Printf.printf "%a%!" API.output_docs api;
      exit 0
  | [|_; "--python-api"|] ->
      Printf.printf "%a%!" API.output_python_api api;
      exit 0
  | _                     ->
  let (file, args) = parse_args ~argv:Sys.argv in
  let state = Document.init ~args ~file in
  match API.run api ~ic:stdin ~oc:stdout state with
  | Ok(_)                    -> exit 0
  | Error(s)                 -> Printf.eprintf "%s\n%!" s; exit 1
  | exception Sys_error(s)   -> Printf.eprintf "Error: %s\n%!" s; exit 1

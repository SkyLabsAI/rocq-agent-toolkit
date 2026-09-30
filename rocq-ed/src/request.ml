open Stdlib_extra.Extra

type empty = |

type insert_keep = [`Atomic | `Successful | `All | `None]

type context = No_context | All_context | Context_lines of int

type print_after = {
  context : context;
  goals : bool;
}

type insert_error = {
  remaining : string;
  unchanged : bool;
}

type position = int * int

type (_, _, _) t =
  | Stop : (unit, unit, empty) t
  | Status : {mode : [`JSON | `Text of print_after]}
      -> (unit, string, empty) t
  | Steps : {count : int option; print : print_after}
      -> (Document.commands_data * string, int, int) t
  | Insert : {text : string; keep : insert_keep; print : print_after}
      -> (Document.commands_data * string, unit, insert_error) t
  | Query : {text : string} -> (unit, string, unit) t
  | Delete : {count : int option; print : print_after}
      -> (string, unit, unit) t
  | Commit : {file : string option; exclude_suffix : bool}
      -> (unit, int, unit) t
  | Goals : (unit, string, empty) t
  | Backwards : {count : int option; print : print_after}
      -> (string, unit, unit) t
  | Goto : {line: int; col: int option; print : print_after}
      -> (string, unit, position option) t

let is_stop : type a b c. (a, b, c) t -> bool = fun r ->
  match r with Stop -> true | _ -> false

let pp_insert_keep ff k =
  match k with
  | `Atomic -> Format.fprintf ff "atomic"
  | `Successful -> Format.fprintf ff "successful"
  | `All -> Format.fprintf ff "all"
  | `None -> Format.fprintf ff "none"

let pp_context ff c =
  match c with
  | No_context -> Format.fprintf ff "none"
  | All_context -> Format.fprintf ff "all"
  | Context_lines lines -> Format.fprintf ff "%i" lines

let pp_print_after ff {context; goals} =
  Format.fprintf ff "{context = %a; goals = %b}" pp_context context goals

let pp_option : 'a Format.pp -> 'a option Format.pp = fun pp ff o ->
  match o with
  | None    -> Format.fprintf ff "None"
  | Some(v) -> Format.fprintf ff "Some(%a)" pp v

let pp : type a b c. (a, b, c) t Format.pp = fun ff r ->
  match r with
  | Stop ->
      Format.fprintf ff "Stop"
  | Status({mode = `JSON}) ->
      Format.fprintf ff "Status({mode = `JSON})"
  | Status({mode = `Text(print)}) ->
      Format.fprintf ff "Status({mode = `Text(%a)})" pp_print_after print
  | Steps({count; print}) ->
      Format.fprintf ff "Steps({count = %a; print = %a})"
        (pp_option Format.pp_print_int) count pp_print_after print
  | Insert({text; keep; print}) ->
      Format.fprintf ff "Insert({text = %S; keep = %a; print = %a})"
        text pp_insert_keep keep pp_print_after print
  | Query({text}) ->
      Format.fprintf ff "Query({text = %S})" text
  | Delete({count; print}) ->
      Format.fprintf ff "Delete({count = %a; print = %a})"
        (pp_option Format.pp_print_int) count pp_print_after print
  | Commit({file; exclude_suffix}) ->
      Format.fprintf ff "Commit({file = %s; exclude_suffix = %b})"
        (Stdlib.Option.value file ~default:"<document file>") exclude_suffix
  | Goals ->
      Format.fprintf ff "Goals"
  | Backwards({count; print}) ->
      Format.fprintf ff "Backwards({count = %a; print = %a})"
        (pp_option Format.pp_print_int) count pp_print_after print
  | Goto({line; col; print}) ->
      Format.fprintf ff "Goto({line = %i; col = %a; print = %a})"
        line (pp_option Format.pp_print_int) col pp_print_after print

let lines : string -> string array = fun s ->
  let lines = Dynarray.create () in
  let line_start = ref 0 in
  let handle_char i c =
    if c = '\n' then begin
      let start = !line_start in
      let line = String.sub s start (i - start + 1) in
      Dynarray.add_last lines line;
      line_start := i + 1
    end
  in
  String.iteri handle_char s;
  let start = !line_start in
  let len = String.length s in
  if start != len then begin
    let line = String.sub s start (len - start) in
    Dynarray.add_last lines line
  end;
  Dynarray.to_array lines

let newline_terminated : string -> bool =
  String.ends_with ~suffix:"\n"

let document_parts d =
  let prefix =
    let prefix = List.rev (Document.rev_prefix d) in
    let filter (Document.{kind; text; _} : Document.processed_item) =
      match kind with `Ghost(_) -> None | _ -> Some(text)
    in
    String.concat "" (List.filter_map filter prefix)
  in
  let suffix =
    let suffix = Document.suffix d in
    let filter (Document.{kind; text} : Document.unprocessed_item) =
      match kind with `Ghost(_) -> None | _ -> Some(text)
    in
    String.concat "" (List.filter_map filter suffix)
  in
  (prefix, suffix)

let run_status d ~context =
  let (prefix, suffix) = document_parts d in
  (* Invariant: all lines end with a newline. *)
  let (prefix, cursor_line, suffix) =
    let prefix = lines prefix in
    let suffix = lines suffix in
    let (prefix, cursor_prefix) =
      match Array.length prefix with 0 -> ([||], "") | n ->
      let last = prefix.(n - 1) in
      match newline_terminated last with
      | true  -> (prefix, "")
      | false -> (Array.sub prefix 0 (n - 1), last)
    in
    let (cursor_suffix, suffix) =
      match Array.length suffix with 0 -> ("\n", [||]) | n ->
      let (first, suffix) = (suffix.(0), Array.sub suffix 1 (n - 1)) in
      let first = first ^ if newline_terminated first then "" else "\n" in
      (first, suffix)
    in
    let len_suffix = Array.length suffix in
    if len_suffix <> 0 then begin
      let last = suffix.(len_suffix - 1) in
      if not (newline_terminated last) then
        suffix.(len_suffix - 1) <- last ^ "\n"
    end;
    (prefix, cursor_prefix ^ "<CURSOR>" ^ cursor_suffix, suffix)
  in
  let lines = Array.concat [prefix; [|cursor_line|]; suffix] in
  let cursor_line = Array.length prefix in
  let nb_lines = Array.length lines in
  let b = Buffer.create 73 in
  let _ =
    match context with
    | None ->
        for i = 0 to nb_lines - 1 do
          Buffer.add_string b (Printf.sprintf "%4i| %s" (i+1) lines.(i))
        done
    | Some(i) ->
        let i1 = max 0 (cursor_line - i) in
        let i2 = min (cursor_line + i) (nb_lines - 1) in
        for i = i1 to i2 do
          Buffer.add_string b (Printf.sprintf "%4i| %s" (i+1) lines.(i))
        done
  in
  Buffer.contents b

let run_json_status d =
  let json = Json.document_to_yojson d in
  Ok(Yojson.Safe.pretty_to_string ~std:true json ^ "\n")

let print_feedback : Document.commands_data -> unit = fun data ->
  let print_feedback_message (m : Rocq_toplevel.feedback_message) =
    match m.level with
    | Feedback.Warning -> Printf.eprintf "Warning: %s\n%!" m.text
    | Feedback.Notice  -> Printf.printf "%s\n%!" m.text
    | _                -> ()
  in
  let print_feedback (data : Document.command_data) =
    List.iter print_feedback_message (data.Rocq_toplevel.feedback_messages)
  in
  List.iter (Option.iter print_feedback) data

let run_goals d =
  match Document.query d ~text:"Locate nat." with
  | Error(_) -> assert false
  | Ok(data) ->
  match data.Rocq_toplevel.proof_state with
  | None -> "Not currently in a proof."
  | Some(p) ->
  let b = Buffer.create 73 in
  let add_focused i goal =
    Buffer.add_string b (Printf.sprintf "Goal %i:\n" (i+1));
    let goal_line s = Buffer.add_string b ("  " ^ s ^ "\n") in
    List.iter goal_line (String.split_on_char '\n' (String.trim goal));
    Buffer.add_string b "\n"
  in
  List.iteri add_focused p.Rocq_toplevel.focused_goals;
  let Rocq_toplevel.{given_up_goals; shelved_goals; unfocused_goals; _} = p in
  let unfocused_goals = List.fold_left (+) 0 unfocused_goals in
  let print cat n =
    if n <> 0 then Buffer.add_string b (Printf.sprintf "%s: %i\n" cat n)
  in
  print "Given up goals" given_up_goals;
  print "Shelved goals" shelved_goals;
  print "Unfocused goals" unfocused_goals;
  Buffer.contents b

let render_print_after d {context; goals} =
  let context =
    match context with
    | No_context -> None
    | All_context -> Some(run_status d ~context:None)
    | Context_lines lines -> Some(run_status d ~context:(Some(lines)))
  in
  match context, goals with
  | None, false -> ""
  | Some(context), false -> context
  | None, true -> run_goals d
  | Some(context), true -> context ^ "\n" ^ run_goals d

let run_steps d ~count ~print =
  let count =
    let len = List.length (Document.suffix d) in
    match count with
    | None        -> len
    | Some(count) -> if count < len then count else len
  in
  try
    let (data, res) = Document.run_steps d ~count in
    let res =
      match res with
      | Ok(()) -> Ok(count)
      | Error(s, (i, None)) -> Error(s, i)
      | Error(_, (i, Some(s, _))) -> Error(s, i)
    in
    ((data, render_print_after d print), res)
  with Invalid_argument(s) -> (([], ""), Error(s, 0))

let sentence_text (sentences : Document.sentence list) =
  let get_text (s : Document.sentence) = s.Document.text in
  String.concat "" (List.map get_text sentences)

let insert_error ?(unchanged=false) remaining = {remaining; unchanged}

let run_insert_keep_all d ~text ~print =
  match Document.replace_suffix ~count:0 d ~text with
  | exception Invalid_argument(s) ->
      (([], ""), Error(s, insert_error ~unchanged:true text))
  | (_, Error(s, remaining)) ->
      (([], ""), Error(s, insert_error ~unchanged:true remaining))
  | (sentences, Ok(())) ->
  let count = List.length sentences in
  let (data, res) = Document.run_steps d ~count in
  let res =
    match res with
    | Ok(()) -> Ok(())
    | Error(s, (nb_processed, None)) ->
        let remaining = sentence_text (List.drop nb_processed sentences) in
        Error(s, insert_error remaining)
    | Error(_, (nb_processed, Some(s, _))) ->
        let remaining = sentence_text (List.drop nb_processed sentences) in
        Error(s, insert_error remaining)
  in
  ((data, render_print_after d print), res)

let run_insert_keep_succeeding d ~text ~print =
  match Document.replace_suffix ~count:0 d ~text with
  | exception Invalid_argument(s) ->
      (([], ""), Error(s, insert_error ~unchanged:true text))
  | (_, Error(s, remaining)) ->
      (([], ""), Error(s, insert_error ~unchanged:true remaining))
  | (sentences, Ok(())) ->
  let count = List.length sentences in
  let (data, res) = Document.run_steps d ~count in
  let res =
    match res with
    | Ok(()) -> Ok(())
    | Error(s, (nb_processed, os)) ->
    let remaining = sentence_text (List.drop nb_processed sentences) in
    let unchanged = nb_processed = 0 in
    Document.clear_suffix ~count:(count - nb_processed) d;
    let s = match os with Some(s, _) -> s | None -> s in
    Error(s, insert_error ~unchanged remaining)
  in
  ((data, render_print_after d print), res)

let run_insert_keep_atomic d ~text ~print =
  let backup = Document.clone d in
  match run_insert_keep_all d ~text ~print with
  | (_, Ok(_)) as res -> res
  | ((data, status), Error(s, e)) ->
      Document.copy_contents ~from:backup d;
      Document.stop backup;
      let header =
        if status = "" then "" else
        let tail =
          " before the failing suffix (prior to document rollback):\n\n"
        in
        match (print.context <> No_context, print.goals) with
        | (false, false) -> ""
        | (true , false) -> "Context" ^ tail
        | (false, true ) -> "Open goals" ^ tail
        | (true , true ) -> "Context and open goals" ^ tail
      in
      ((data, header ^ status), Error(s, {e with unchanged = true}))
  | exception e ->
      Document.copy_contents ~from:backup d;
      Document.stop backup;
      raise e

let run_insert_keep_none d ~text ~print =
  Document.with_rollback d @@ fun () ->
  let ((data, status), res) = run_insert_keep_all d ~text ~print in
  let header =
    if status = "" then "" else
    let tail =
      let tail = " (prior to document rollback):\n\n" in
      match res with
      | Ok(_) -> " after the inserted text" ^ tail
      | Error(_) -> " before the failing suffix" ^ tail
    in
    match (print.context <> No_context, print.goals) with
    | (false, false) -> ""
    | (true , false) -> "Context" ^ tail
    | (false, true ) -> "Open goals" ^ tail
    | (true , true ) -> "Context and open goals" ^ tail
  in
  let res =
    Result.map_error (fun (s, e) -> (s, {e with unchanged = true})) res
  in
  ((data, header ^ status), res) 

let run_insert d ~text ~keep ~print =
  match keep with
  | `Atomic -> run_insert_keep_atomic d ~text ~print
  | `Successful -> run_insert_keep_succeeding d ~text ~print
  | `All -> run_insert_keep_all d ~text ~print
  | `None -> run_insert_keep_none d ~text ~print

let run_query d ~text =
  let text = String.trim text in
  match Document.query_text_all d ~text with
  | Ok(ls) -> Ok(String.concat "\n" ls)
  | Error(s) -> Error(s, ())

let run_delete d ~count ~print =
  try
    Document.clear_suffix ?count d;
    (render_print_after d print, Ok())
  with Invalid_argument(s) ->
    ("", Error(s, ()))

let run_commit d ~file ~exclude_suffix =
  (* [commit] writes the unprocessed suffix by default; callers get the number
     of unprocessed items that were written so they can refuse or warn. *)
  (* Only unprocessed commands matter; trailing blanks are not proof text. *)
  let is_command (it : Document.unprocessed_item) =
    match it.kind with `Blanks -> false | `Command(_) | `Ghost(_) -> true
  in
  let suffix_len = List.length (List.filter is_command (Document.suffix d)) in
  let include_suffix = not exclude_suffix in
  match Document.commit ?file ~include_suffix d with
  | Ok(()) -> Ok(if include_suffix then suffix_len else 0)
  | Error(s) -> Error(s, ())

let run_backwards d ~count ~print =
  assert (match count with None -> true | Some(i) -> 0 <= i);
  let cursor_index = Document.cursor_index d in
  let index = match count with None -> 0 | Some(n) -> cursor_index - n in
  match index < 0 with
  | true  ->
      let msg =
        Printf.sprintf "the cursor can only move up to %i steps backwards"
          cursor_index
      in
      ("", Error(msg, ()))
  | false ->
      Document.revert_before d ~index;
      (render_print_after d print, Ok(()))

let cursor_position d =
  let (prefix, _) = document_parts d in
  let (line, line_text) =
    let line = ref 1 in
    let line_start = ref 0 in
    String.iteri (fun i c ->
      if c = '\n' then (incr line; line_start := i + 1)
    ) prefix;
    let len_prefix = String.length prefix in
    (!line, String.sub prefix !line_start (len_prefix - !line_start))
  in
  let col =
    Uuseg_string.fold_utf_8 `Grapheme_cluster
      (fun col _ -> col + 1) 1 line_text
  in
  (line, col)

let run_goto d ~line ~col ~print =
  assert (line > 0 && Stdlib.Option.value ~default:1 col > 0);
  (* Collect the text of all document items. *)
  let items =
    let get_text (Document.{kind; text; _} : Document.processed_item) =
      match kind with `Ghost(_) -> "" | _ -> text
    in
    let prefix = List.rev_map get_text (Document.rev_prefix d) in
    let get_text (Document.{kind; text} : Document.unprocessed_item) =
      match kind with `Ghost(_) -> "" | _ -> text
    in
    let suffix = List.map get_text (Document.suffix d) in
    prefix @ suffix
  in
  (* Get the line representation of the document. *)
  let lines = lines (String.concat "" items) in
  let nb_lines = Array.length lines in
  (* Check that there are enough lines. *)
  match nb_lines < line with
  | true  ->
      let msg = Printf.sprintf "no item on line %i" line in
      ("", Error(msg, None))
  | false ->
  (* Finding the byte offset of the start of the line, and the line length. *)
  let line_start_off =
    let off = ref 0 in
    for i = 0 to line - 2 do off := !off + String.length lines.(i) done; !off
  in
  let line_len = String.length lines.(line - 1) in
  let line_end_off = line_start_off + line_len - 1 in
  (* Collecting the candidate items, with their index. *)
  let rec collect acc ~off ~index items =
    match items with [] -> List.rev acc | item :: items ->
    let len = String.length item in
    let next_off = off + len in
    let continue acc =
      collect acc ~off:next_off ~index:(index + 1) items
    in
    if next_off < line_start_off then
      continue acc
    else if line_start_off <= next_off && off <= line_end_off then
      continue ((item, index, off, next_off - 1) :: acc)
    else
      List.rev acc
  in
  let candidates = collect [] ~off:0 ~index:0 items in
  assert (List.length candidates > 0);
  (* Trim excess bits of candidates (falling on the previous or next line). *)
  let trim (item, index, off_start, off_end) =
    let trim_l = max 0 (line_start_off - off_start) in
    let trim_r = max 0 (off_end - line_end_off) in
    let len = String.length item - trim_l - trim_r in
    (String.sub item trim_l len, index, off_start, off_end)
  in
  let candidates = List.map trim candidates in
  let _ =
    let line_text = List.map (fun (text, _, _, _) -> text) candidates in
    let line_text = String.concat "" line_text in
    assert (line_text = lines.(line - 1))
  in
  (* Select the index. *)
  let index =
    match col with
    | None      ->
        let (_, index, _, _) = List.hd candidates in
        Ok(index)
    | Some(col) ->
        let rec find_col n candidates =
          match candidates with
          | [] ->
              let msg =
                Printf.sprintf "no item on line %i, column %i" line col
              in
              Error(msg, None)
          | (text, index, _, _) :: candidates ->
              let next_n =
                Uuseg_string.fold_utf_8 `Grapheme_cluster
                  (fun n _ -> n + 1) n text
              in
              if col <= next_n then Ok(index) else find_col next_n candidates
        in
        find_col 0 candidates
  in
  match index with
  | Error(msg, pos) -> ("", Error(msg, pos))
  | Ok(index) ->
  let res =
    match Document.go_to d ~index with
    | Ok(()) -> Ok(())
    | Error(msg, None)
    | Error(_, Some(msg, _)) -> Error(msg, Some(cursor_position d))
  in
  (render_print_after d print, res)

let run : type a b c. Document.t -> (a, b, c) t ->
    a * (b, string * c) Result.t = fun d r ->
  match r with
  | Stop -> ((), Ok(()))
  | Status({mode = `JSON}) -> ((), run_json_status d)
  | Status({mode = `Text(print)}) -> ((), Ok(render_print_after d print))
  | Steps({count; print}) -> run_steps d ~count ~print
  | Insert({text; keep; print}) -> run_insert d ~text ~keep ~print
  | Query({text}) -> ((), run_query d ~text)
  | Delete({count; print}) -> run_delete d ~count ~print
  | Commit({file; exclude_suffix}) -> ((), run_commit d ~file ~exclude_suffix)
  | Goals -> ((), Ok(run_goals d))
  | Backwards({count; print}) -> run_backwards d ~count ~print
  | Goto({line; col; print}) -> run_goto d ~line ~col ~print

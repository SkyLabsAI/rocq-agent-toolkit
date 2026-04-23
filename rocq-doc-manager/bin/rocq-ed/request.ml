open Stdlib_extra.Extra

type empty = |

type (_, _) t =
  | Stop : (unit, empty) t
  | Status : {context : int option} -> (string, empty) t
  | Steps : {count : int} -> (unit, int) t
  | Insert : {text : string} -> (unit, string) t
  | Query : {text : string} -> (string, unit) t
  | Delete : {count : int} -> (unit, unit) t
  | Commit : (unit, unit) t
  | Goals : (string, empty) t
  | Undo : {count : int} -> (unit, unit) t
  | Goto : {line: int; col: int option} -> (unit, int) t

let is_stop : type a b. (a, b) t -> bool = fun r ->
  match r with Stop -> true | _ -> false

let pp : type a b. (a, b) t Format.pp = fun ff r ->
  match r with
  | Stop ->
      Format.fprintf ff "Stop"
  | Status({context = None}) ->
      Format.fprintf ff "Status({context = None})"
  | Status({context = Some(i)}) ->
      Format.fprintf ff "Status({context = %i})" i
  | Steps({count}) ->
      Format.fprintf ff "Steps({count = %i})" count
  | Insert({text}) ->
      Format.fprintf ff "Insert({text = %S})" text
  | Query({text}) ->
      Format.fprintf ff "Query({text = %S})" text
  | Delete({count}) ->
      Format.fprintf ff "Delete({count = %i})" count
  | Commit ->
      Format.fprintf ff "Commit"
  | Goals ->
      Format.fprintf ff "Goals"
  | Undo({count}) ->
      Format.fprintf ff "Undo({count = %i})" count
  | Goto({line; col = None}) ->
      Format.fprintf ff "Goto({line = %i; col = None})" line
  | Goto({line; col = Some(col)}) ->
      Format.fprintf ff "Goto({line = %i; col = %i})" line col

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

let run_status d ~context =
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
  Ok(Buffer.contents b)

let run_steps d ~count =
  match Document.run_steps d ~count with
  | Ok(()) -> Ok(())
  | Error(s, (i, None)) -> Error(s, i)
  | Error(_, (i, Some(s, _))) -> Error(s, i)
  | exception Invalid_argument(s) -> Error(s, 0)

let run_insert d ~text =
  match Document.split_sentences d ~text with
  | exception Invalid_argument(s) -> Error(s, text)
  | (sentences, res) ->
  let rec run_sentences (sentences : Document.sentence list) =
    match sentences with
    | [] -> ([], None)
    | Document.{kind; text} as s :: sentences ->
    let err =
      match kind with
      | `Blanks ->
          begin
            try Document.insert_blanks d ~text; None with
            | Invalid_argument(s) -> Some(s)
          end
      | `Command(_) ->
          begin
            match Document.insert_command d ~text with
            | Ok(_) -> None
            | Error(s, _) -> Some(s)
            | exception Invalid_argument(s) -> Some(s)
          end
    in
    match err with
    | None -> run_sentences sentences
    | _ -> (s :: sentences, err)
  in
  let get_text (d : Document.sentence) = d.Document.text in
  match (run_sentences sentences, res) with
  | ((_, None), Ok(())) -> Ok(())
  | ((_, None), Error(s, remaining)) -> Error(s, remaining)
  | ((sentences, Some(s)), Ok(())) ->
      let remaining = List.map get_text sentences in
      let remaining = String.concat "" remaining in
      Error(s, remaining)
  | ((sentences, Some(s)), Error(_, remaining)) ->
      let remaining = List.map get_text sentences @ [remaining] in
      let remaining = String.concat "" remaining in
      Error(s, remaining)

let run_query d ~text =
  let text = String.trim text in
  match Document.query_text_all d ~text with
  | Ok(ls) -> Ok(String.concat "\n" ls)
  | Error(s) -> Error(s, ())

let run_delete d ~count =
  try Ok(Document.clear_suffix ~count d) with
  | Invalid_argument(s) -> Error(s, ())

let run_commit d =
  let res = Document.commit d in
  Result.map_error (fun s -> (s, ())) res

let run_goals d =
  match Document.query d ~text:"Locate nat." with
  | Error(_) -> assert false
  | Ok(data) ->
  match data.Rocq_toplevel.proof_state with
  | None -> Ok("Not currently in a proof.")
  | Some(p) ->
  let b = Buffer.create 73 in
  let add_focused i goal =
    Buffer.add_string b (Printf.sprintf "Goal %i:\n" (i+1));
    let goal_line s = Buffer.add_string b ("  " ^ s ^ "\n") in
    List.iter goal_line (String.split_on_char '\n' (String.trim goal))
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
  Ok(Buffer.contents b)

let run_undo d ~count =
  let cursor_index = Document.cursor_index d in
  let index = cursor_index - count in
  if index < 0 then
    Error("invalid count (not enough items to undo)", ())
  else
    Ok(Document.revert_before d ~index)

let run_goto d ~line ~col =
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
  | true  -> Error("no item on the given line", Document.cursor_index d)
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
              Error("no item on the given column", Document.cursor_index d)
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
  | Error(msg, i) -> Error(msg, i)
  | Ok(index)  ->
  match Document.go_to d ~index with
  | Ok(()) -> Ok(())
  | Error(msg, _) -> Error(msg, Document.cursor_index d)

let run : type a b. Document.t -> (a, b) t ->
    (a, string * b) Result.t = fun d r ->
  match r with
  | Stop              -> Ok(())
  | Status({context}) -> run_status d ~context
  | Steps({count})    -> run_steps d ~count
  | Insert({text})    -> run_insert d ~text
  | Query({text})     -> run_query d ~text
  | Delete({count})   -> run_delete d ~count
  | Commit            -> run_commit d
  | Goals             -> run_goals d
  | Undo({count})     -> run_undo d ~count
  | Goto({line; col}) -> run_goto d ~line ~col

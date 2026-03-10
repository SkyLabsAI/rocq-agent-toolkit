open Rocq_split

let kind_to_yojson k =
  match k with
  | `Blanks     -> `String("blanks")
  | `Command(c) -> Rocq_vernac_entry.command_to_yojson c

let sentence_to_json {kind; text; bp; ep} =
  `Assoc([
    ("kind", kind_to_yojson kind);
    ("text", `String(text)      );
    ("bp"  , `Int(bp)           );
    ("ep"  , `Int(ep)           );
  ])

let output_error error {parsed_sentences = sentences; error_loc = loc} =
  let loc = match loc with Some(loc) -> Rocq_loc.to_yojson loc | _ -> `Null in
  let sentences = List.map sentence_to_json sentences in
  let json =
    `Assoc([
      ("error", `String(error)  );
      ("loc"  , loc             );
      ("Items", `List(sentences));
    ])
  in
  Format.printf "%a\n%!" (Yojson.Safe.pretty_print ~std:true) json

let output_result file {dirpath; sentences} =
  let dirpath = Names.DirPath.to_string dirpath in
  let sentences = List.map sentence_to_json sentences in
  let json =
    `Assoc([
      ("file"   , `String(file)   );
      ("dirpath", `String(dirpath));
      ("items"  , `List(sentences));
    ])
  in
  Format.printf "%a\n%!" (Yojson.Safe.pretty_print ~std:true) json

let _ =
  let usage i =
    let prog = Sys.argv.(0) in
    Printf.eprintf "Usage: %s [-h|-help|--help] FILE [-- ROCQARGS]\n%!" prog;
    exit i
  in
  let (file, args) =
    let (argv, args) =
      match Array.find_index (String.equal "--") Sys.argv with
      | None    -> (Sys.argv, [])
      | Some(i) ->
      let argv = Array.sub Sys.argv 0 i in
      let args = Array.sub Sys.argv (i+1) (Array.length Sys.argv - i - 1) in
      (argv, Array.to_list args)
    in
    let argv = List.tl (Array.to_list argv) in
    let is_help arg = List.mem arg ["-h"; "-help"; "--help"] in
    match List.exists is_help argv with
    | true  -> usage 0
    | false ->
    match argv with
    | [file] -> (file, args)
    | _      -> usage 1
  in
  match Rocq_split.split_file ~file ~args with
  | Ok(data)       -> output_result file data
  | Error(s, data) -> output_error s data; exit 1

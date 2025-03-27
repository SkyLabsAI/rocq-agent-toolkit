let _ =
  let state = Rocq_split.init ~argv:Sys.argv in
  let (res, _) = Rocq_split.get state in
  match res with
  | Error(s)      -> Printf.eprintf "%s%!" s; exit 1
  | Ok(sentences) ->
  let items = `List(List.map Rocq_split.sentence_to_yojson sentences) in
  let file = `String(Rocq_split.get_file state) in
  let dirpath = Rocq_split.get_dirpath state in
  let dirpath = `String(Names.DirPath.to_string dirpath) in
  let pp_json ff json = Yojson.Safe.pretty_print ~std:true ff json in
  Format.printf "%a\n%!" pp_json
    (`Assoc([("file", file); ("dirpath", dirpath); ("items", items)]))

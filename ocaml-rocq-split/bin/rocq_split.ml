let output_error ?loc error =
  let loc = match loc with Some(loc) -> Rocq_loc.to_yojson loc | _ -> `Null in
  let json =
    `Assoc([
      ("error", `String(error));
      ("loc"  , loc           );
    ])
  in
  Format.printf "%a\n%!" (Yojson.Safe.pretty_print ~std:true) json

let output_result ~file ~dirpath ~items =
  let json =
    `Assoc([
      ("file"   , `String(file)   );
      ("dirpath", `String(dirpath));
      ("items"  , `List(items)    );
    ])
  in
  Format.printf "%a\n%!" (Yojson.Safe.pretty_print ~std:true) json

let _ =
  let state =
    match Rocq_split.init ~argv:Sys.argv with
    | Ok(state) -> state
    | Error(s)  -> output_error s; exit 1
  in
  let (res, _) = Rocq_split.get state in
  let sentences =
    match res with
    | Ok(sentences) -> sentences
    | Error(loc, s) -> output_error ?loc s; exit 1
  in
  let file = Rocq_split.get_file state in
  let dirpath = Names.DirPath.to_string (Rocq_split.get_dirpath state) in
  let items = List.map Rocq_split.sentence_to_yojson sentences in
  output_result ~file ~dirpath ~items

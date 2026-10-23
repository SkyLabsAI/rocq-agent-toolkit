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
  let error s =
    let json = `Assoc([("error", `String(s)); ("loc", `Null)]) in
    Format.printf "%a\n%!" (Yojson.Safe.pretty_print ~std:true) json;
    exit 1
  in
  let toplevel =
    let args = "-topfile" :: file :: args in
    try Rocq_toplevel.init ~args with Failure(s) ->
    error (Printf.sprintf "Failed to initialized the toplevel (%s)" s)
  in
  let text =
    try In_channel.(with_open_text file input_all) with Sys_error(s) ->
    error (Printf.sprintf "System error (%s)" s)
  in
  let source = Loc.InFile({dirpath = None; file}) in
  let res = Rocq_toplevel.split toplevel ~text ~loc:(Loc.initial source) in
  Rocq_toplevel.stop toplevel;
  match res with
  | Ok(data) ->
      let json = Rocq_toplevel.split_data_to_yojson data in
      Format.printf "%a\n%!" (Yojson.Safe.pretty_print ~std:true) json
  | Error(e) ->
      let json = Rocq_toplevel.split_error_to_yojson e in
      Format.printf "%a\n%!" (Yojson.Safe.pretty_print ~std:true) json;
      exit 1

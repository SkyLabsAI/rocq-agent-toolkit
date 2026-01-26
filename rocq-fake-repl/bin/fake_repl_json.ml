(** filters out [-topfile] *)
let get_args argv : string list =
  let rec go i : string list =
    if i >= Array.length argv then []
    else
      if argv.(i) = "-topfile" then go (i+2)
      else argv.(i) :: go (i + 1)
  in go 1

let env key : Yojson.t =
  try `String (Sys.getenv key)
  with Not_found -> `Null

let _ =
  let result : Yojson.t =
    `Assoc [
      ("args", `List (List.map (fun s -> `String s) (get_args Sys.argv)));
      ("ROCQPATH", env "ROCQPATH");
      ("ROCQLIB", env "ROCQLIB");
      ("OCAMLPATH", env "OCAMLPATH")
    ]
  in
  Yojson.pretty_to_channel stdout result

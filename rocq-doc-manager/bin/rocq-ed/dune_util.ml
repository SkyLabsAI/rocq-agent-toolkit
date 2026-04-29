open Stdlib_extra.Extra
open Panic

type config = {
  no_build : bool;
  jobs : int option;
  display : string;
}

let get_dune_root : unit -> string = fun () ->
  let cmd = "dune" in
  (* TODO: We cannot suppress dune's output of the form "Entering directory [..]" despite specifying the flag here. *)
  let args = ["exec"; "--no-print-directory"; "--"; "printenv"; "DUNE_SOURCEROOT"] in
  let temp = Filename.temp_file "temp" ".cli" in
  (* TODO: We also cannot suppress the dune output ending up in our own output despite specifying Null below. *)
  match Cmdutil.(run ~cmd ~stderr:Null ~stdout:(File(temp)) args) with
  | Error(_,s) ->
      Fileutil.remove_file temp;
      panic "Error: cannot find DUNE_SOURCEROOT of (process %s)." (Sys.getcwd()) s
  | Ok(()) ->
  let lines = Fileutil.read_lines temp in
  Fileutil.remove_file temp;
  let result = String.trim (List.hd lines) in
  if String.ends_with ~suffix:"/" result then
    String.take (String.length result - 1) result
  else
    result

let get_args : config -> Filepath.t -> string list = fun config rocq_file ->
  let cwd = Sys.getcwd () in
  let dune_root = get_dune_root () in
  assert (String.starts_with ~prefix:dune_root cwd);
  let relative_path =
    let path = String.drop (String.length dune_root) cwd in
    if String.starts_with ~prefix:"/" path then
      String.drop 1 path
    else
      path
  in
  let rocq_file = Filename.concat relative_path rocq_file in
  (* Temporarily switch to [dune_root] to work around inconsistencies between
     cram tests and live environments. *)
  Sys.chdir dune_root;
  let args =
    let display = Printf.sprintf "--display=%s" config.display in
    let jobs = Option.map (Printf.sprintf "-j%i") config.jobs in
    let jobs = match jobs with None -> [] | Some(s) -> [s] in
    let no_build = if config.no_build then ["--no-build"] else [] in
    let args = ["rocq"; "top"; display; "--toplevel=rocq-fake-repl"] in
    args @ jobs @ no_build @ [rocq_file]
  in
  let temp = Filename.temp_file "temp" ".cli" in
  match Cmdutil.(run ~cmd:"dune" ~stderr:Shell ~stdout:(File(temp)) args) with
  | Error(_,s) ->
      Sys.chdir cwd;
      Fileutil.remove_file temp;
      panic "Error: cannot get CLI arguments for %S (process %s)." rocq_file s
  | Ok(())     ->
  Sys.chdir cwd;
  let lines = Fileutil.read_lines temp in
  Fileutil.remove_file temp; lines

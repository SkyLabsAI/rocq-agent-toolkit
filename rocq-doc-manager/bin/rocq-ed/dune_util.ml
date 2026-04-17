open Stdlib_extra.Extra
open Panic

type config = {
  no_build : bool;
  jobs : int option;
  display : string;
}

let get_args : config -> Filepath.t -> string list = fun config rocq_file ->
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
      Fileutil.remove_file temp;
      panic "Error: cannot get CLI arguments for %S (process %s)." rocq_file s
  | Ok(())     ->
  let lines = Fileutil.read_lines temp in
  Fileutil.remove_file temp; lines

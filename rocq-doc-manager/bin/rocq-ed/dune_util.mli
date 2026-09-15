open Stdlib_extra.Extra

val get_dune_root : unit -> Filepath.t

type config = {
  no_build : bool;
  jobs : int option;
  display : string;
}

val get_args : config -> Filepath.t -> string list

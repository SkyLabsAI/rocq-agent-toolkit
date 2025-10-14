(** [split ~argv] splits the [argv] array into two parts: "program arguments",
    and Rocq arguments. All arguments appearing after the separator ["--"] are
    considered to be Rocq arguments, and all arguments appearing before it are
    considered to be program arguments. The separator itself is excluded. *)
val split : argv:string array -> string array * string list

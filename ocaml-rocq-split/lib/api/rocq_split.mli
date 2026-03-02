(** Rocq sentence-splitting *)

(** Stripped-down version of [Synterp.synterp_entry]. *)
type entry =
  | EVernacNoop
  | EVernacNotation
  | EVernacBeginSection of Names.lident
  | EVernacEndSegment of Names.lident
  | EVernacRequire
  | EVernacImport
  | EVernacDeclareModule of Lib.export * Names.lident
  | EVernacDefineModule of Lib.export * Names.lident
  | EVernacDeclareModuleType of Names.lident
  | EVernacInclude
  | EVernacSetOption
  | EVernacLoad
  | EVernacExtend

(** AST of a Rocq vernacular command (slightly simplified). *)
type command = entry Vernacexpr.vernac_expr_gen CAst.t

(** Rocq sentence (vernacular command, or sequence of blank caracters). *)
type sentence = {
  kind : [`Command of command | `Blanks];
  (** Sentence kind: an actual command or a sequence of blank characters. *)
  text : string;
  (** Full text of the sentence. *)
  bp : int;
  (** Byte offset of the first character of the sentence in the file. *)
  ep : int;
  (** Byte offset of the first character after the sentence in the file. *)
}

(** Data returned by the sentence-splitter. *)
type split_data = {
  dirpath : Names.DirPath.t;
  (** Rocq directory path for the file that was sentence-split. *)
  sentences : sentence list;
  (** List of parsed sentences. *)
}

(** Data returned in case of sentence-splitting error. *)
type split_error = {
  parsed_sentences : sentence list;
  (** Successfully parsed sentences before the error. *)
  error_loc : Rocq_loc.t option;
  (** Location for the error, if any. *)
}

(** [split_file ~file ~args] runs the sentence-splitter on the given Rocq file
    [file], using [args] as Rocq command-line arguments. *)
val split_file : file:string -> args:string list
  -> (split_data, string * split_error) result

(** [split_string ~file ~args contents] is like [split_string ~file ~args] but
    [contents] is considered to be the contents of the file (i.e., the file is
    never actually opened / read). *)
val split_string : file:string -> args:string list -> string
  -> (split_data, string * split_error) result

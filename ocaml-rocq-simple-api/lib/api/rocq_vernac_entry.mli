(** Stripped-down version of [Synterp.synterp_entry]. *)
type entry = Rocq_simple_api_internal.Rocq_vernac_entry.entry =
  | EVernacNoop
  | EVernacNotation
  | EVernacBeginSection of Names.lident
  | EVernacEndSegment of Names.lident
  | EVernacRequire
  | EVernacImport
  | EVernacDeclareModule of Names.lident
  | EVernacDefineModule of Names.lident
  | EVernacDeclareModuleType of Names.lident
  | EVernacInclude
  | EVernacSetOption
  | EVernacLoad
  | EVernacExtend

(** AST of a Rocq vernacular command (slightly simplified). *)
type command = entry Vernacexpr.vernac_expr_gen CAst.t

(** [command_tag c] returns a representation of the command kind of [c], based
    on the corresponding OCaml constructor name. *)
val command_tag : command -> string

(** [command_to_yojson c] produces a simplistic description of [c] as JSON. *)
val command_to_yojson : command -> Yojson.Safe.t

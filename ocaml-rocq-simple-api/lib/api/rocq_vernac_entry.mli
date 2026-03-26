(** Stripped-down version of [Synterp.synterp_entry]. *)
type entry = Rocq_simple_api_internal.Rocq_vernac_entry.entry =
  | EVernacNoop
  | EVernacNotation
  | EVernacBeginSection of Names.lident
  | EVernacEndSegment of Names.lident
  | EVernacRequire
  | EVernacImport
  | EVernacDeclareModule of Names.lident
  | EVernacDefineModule of Names.lident * bool
  | EVernacDeclareModuleType of Names.lident * bool
  | EVernacInclude
  | EVernacSetOption
  | EVernacLoad
  | EVernacExtend

(** AST of a Rocq vernacular command (slightly simplified). *)
type command = entry Vernacexpr.vernac_expr_gen CAst.t

(** [command_tag c] returns a representation of the command kind of [c], based
    on the corresponding OCaml constructor name. *)
val command_tag : command -> string

(** [command_tags] collects all the possible outputs of [command_tag]. *)
val command_tags : string array

(** [command_id_pure c] indicates whether the command is pure (for the synterp
    phase), which means that it does not influence parsing. *)
val command_is_pure : command -> bool

(** [command_to_yojson c] produces a simplistic description of [c] as JSON. *)
val command_to_yojson : command -> Yojson.Safe.t

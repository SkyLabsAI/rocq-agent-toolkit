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

type command = entry Vernacexpr.vernac_expr_gen CAst.t

type sentence = {
  kind : [`Command of command | `Blanks];
  text : string;
  bp : int;
  ep : int;
}

type split_data = {
  dirpath : Names.DirPath.t;
  sentences : sentence list;
}

type split_error = {
  parsed_sentences : sentence list;
  error_loc : Rocq_loc.t option;
}

type config = {
  file : string;
  args : string list;
  contents : string option;
}

type res = {
  commands : command list;
  feedback : Feedback.feedback list;
  result : (Names.DirPath.t, string * Rocq_loc.t option) result;
}

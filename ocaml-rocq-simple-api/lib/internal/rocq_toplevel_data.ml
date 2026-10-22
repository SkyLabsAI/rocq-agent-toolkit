type level = Feedback.level

let level_to_yojson level =
  let open Feedback in
  match level with
  | Debug -> `String("debug")
  | Info -> `String("info")
  | Notice -> `String("notice")
  | Warning -> `String("warning")
  | Error -> `String("error")

type constant = Names.Constant.t

let constant_to_yojson c = `String(Names.Constant.to_string c)

type mutind = Names.MutInd.t

let mutind_to_yojson m = `String(Names.MutInd.to_string m)

type quickfix = {
  loc : Rocq_loc.t;
  text : string;
}
[@@deriving to_yojson]

type feedback_message = {
  level : level;
  loc : (Rocq_loc.t option [@default None]);
  quickfix : (quickfix list [@default []]);
  text : string;
}
[@@deriving to_yojson]

type globrefs_diff = {
  added_constants : (constant list [@default []]);
  removed_constants : (constant list [@default []]);
  added_inductives : (mutind list [@default []]);
  removed_inductives : (mutind list [@default []]);
}
[@@deriving to_yojson]

let empty_globrefs_diff = {
  added_constants = [];
  removed_constants = [];
  added_inductives = [];
  removed_inductives = [];
}

type structured_hyp = {
  name : string;
  def : (string option [@default None]);
  hyp_type : string [@key "type"];
}
[@@deriving to_yojson]

type structured_goal = {
  hyps : structured_hyp list;
  goal : string;
}
[@@deriving to_yojson]

type proof_state = {
  given_up_goals : (int [@default 0]);
  shelved_goals : (int [@default 0]);
  unfocused_goals : (int list [@default []]);
  focused_goals : (string list [@default []]);
}
[@@deriving to_yojson]

type run_data = {
  globrefs_diff : (globrefs_diff [@default empty_globrefs_diff]);
  feedback_messages : (feedback_message list [@default []]);
  synterp_ast : Rocq_vernac_entry.command;
  proof_state : (proof_state option [@default None]);
  loc : (Rocq_loc.t option [@default None]);
}
[@@deriving to_yojson]

type run_error = {
  error_loc : (Rocq_loc.t option [@default None]);
  feedback_messages : (feedback_message list [@default []]);
  loc : (Rocq_loc.t option [@default None]);
}
[@@deriving to_yojson]

type command = Rocq_vernac_entry.command

type item_kind = [`Command of command | `Blanks]

let item_kind_to_yojson k =
  match k with
  | `Command(c) -> Rocq_vernac_entry.command_to_yojson c
  | `Blanks -> `String("blanks")

type item = {
  kind : item_kind;
  text : string;
  bp : int;
  ep : int;
}
[@@deriving to_yojson]

type split_data = {
  items : item list;
}
[@@deriving to_yojson]

type split_error = {
  parsed_items : item list [@key "items"];
  leftover : string;
  error_text : string [@key "error"];
  error_loc : Rocq_loc.t option [@key "loc"];
}
[@@deriving to_yojson]

type raw_split_data = {
  commands : command list;
  feedback : Feedback.feedback list;
  result : (unit, string * Rocq_loc.t option) result;
}

type empty = |

type (_, _) cmd =
  | Run : {loc : Loc.t; text : string} -> (run_data, string * run_error) cmd
  | BackTo : {sid : int} -> (unit, string) cmd
  | Fork : {pipe_in : string; pipe_out : string} -> (int, string) cmd
  | StructuredGoals : (structured_goal list option, empty) cmd
  | LocAfterBlanks : {loc : Loc.t; text : string} -> (Rocq_loc.t, string) cmd
  | Split : {loc : Loc.t; text : string; sid : int option} ->
      (raw_split_data, empty) cmd

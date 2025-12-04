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
  proof_state : (proof_state option [@default None])
}
[@@deriving to_yojson]

type run_error = {
  error_loc : (Rocq_loc.t option [@default None]);
  feedback_messages : (feedback_message list [@default []]);
}
[@@deriving to_yojson]

type (_, _) command =
  | Run : {off : int; text : string} -> (run_data, string * run_error) command
  | BackTo : {sid : int} -> (unit, string) command

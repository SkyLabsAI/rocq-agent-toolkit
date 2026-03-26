type json = Yojson.Safe.t

let rec seqn (low : int) (high : int) : int list =
  if low > high then [] else low :: seqn (low + 1) high

let or_var_json : int Locus.or_var -> json = function
  | Locus.ArgArg n -> `Int n
  | Locus.ArgVar _ -> `Null

let goal_range_selector_json : Proofview.goal_range_selector -> json list =
  let open Proofview in
  function
  | NthSelector i -> [ `Int i ]
  | RangeSelector (low, high) -> List.map (fun n -> `Int n) (seqn low high)
  | IdSelector n -> [ `String (Names.Id.to_string n) ]

let goal_select_json : Goal_select.t -> json =
  let open Goal_select in
  function
  | SelectAlreadyFocused -> `Null
  | SelectList sels -> `List (List.concat_map goal_range_selector_json sels)
  | SelectAll -> `Bool true

let to_json env evd : Ltac_plugin.Tacexpr.raw_tactic_expr -> json =
  let rec to_json tac =
    let default () =
      `String
        (Pp.string_of_ppcmds (Ltac_plugin.Pptactic.pr_raw_tactic env evd tac))
    in
    let to_json_list = List.map to_json in
    let to_json_array ary = List.map to_json (Array.to_list ary) in
    let tag, args =
      let open Ltac_plugin.Tacexpr in
      match tac.v with
      | TacThen (a, b) -> ("Then", [ to_json a; to_json b ])
      | TacDispatch bs -> ("Dispatch", to_json_list bs)
      | TacExtendTac (tas, tac, tas2) ->
          ( "ExtendTac",
            [
              `List (to_json_array tas); to_json tac; `List (to_json_array tas2);
            ] )
      | TacThens (a, bs) -> ("Thens", [ to_json a; `List (to_json_list bs) ])
      | TacThens3parts (a, bs, b, bs2) ->
          ( "Thens3",
            [
              to_json a;
              `List (to_json_array bs);
              to_json b;
              `List (to_json_array bs2);
            ] )
      | TacFirst bs -> ("First", to_json_list bs)
      | TacSolve bs -> ("Solve", to_json_list bs)
      | TacTry tac -> ("Try", [ to_json tac ])
      | TacOr (a, b) -> ("Or", [ to_json a; to_json b ])
      | TacOnce tac -> ("Once", [ to_json tac ])
      | TacExactlyOnce tac -> ("ExactlyOnce", [ to_json tac ])
      | TacIfThenCatch (a, b, c) ->
          ("IfThenCatch", [ to_json a; to_json b; to_json c ])
      | TacOrelse (a, b) -> ("OrElse", [ to_json a; to_json b ])
      | TacDo (n, tac) -> ("Do", [ or_var_json n; to_json tac ])
      | TacTimeout (_, tac) -> ("Timeout", [ to_json tac ])
      | TacTime (_, tac) -> ("Time", [ to_json tac ])
      | TacRepeat tac -> ("Repeat", [ to_json tac ])
      | TacProgress tac -> ("Progress", [ to_json tac ])
      | TacFail _ -> ("Fail", [ default () ])
      | TacId _ -> ("Idtac", [ default () ])
      | TacSelect (goal, tac) ->
          ("Select", [ goal_select_json goal; to_json tac ])
      | _ -> ("Atom", [ default () ])
    in
    `List (`String tag :: args)
  in
  to_json

let explain env evd tac =
  Feedback.msg_info
    Pp.(str (Yojson.Safe.pretty_to_string ~std:true (to_json env evd tac)))

let vernac_data_to_yojson v =
  let attrs = Vernac_data_util.command_attrs v in
  let fields = [("kind", `String(Rocq_vernac_entry.command_tag v))] in
  let fields =
    let controls = Rocq_vernac_entry.command_controls v in
    match List.map (fun s -> `String(s)) controls with
    | [] -> fields
    | cs -> fields @ [("controls", `List(cs))]
  in
  let fields =
    match Rocq_vernac_entry.command_is_pure v with
    | true  -> fields @ [("pure", `Bool(true))]
    | false -> fields
  in
  let fields =
    match attrs with
    | [] -> fields
    | _  -> fields @ [("attrs", `Assoc(attrs))]
  in
  `Assoc(fields)

let item_kind_to_yojson = function
  | `Blanks     -> ("blanks", None)
  | `Command(d) -> ("command", Some(vernac_data_to_yojson d))
  | `Ghost(d)   -> ("ghost", Some(vernac_data_to_yojson d))

let prefix_item_to_yojson
    (Document.{kind; off; text; _} : Document.processed_item) =
  let (kind, data) = item_kind_to_yojson kind in
  let fields =
    [("kind", `String(kind)); ("offset", `Int(off)); ("text", `String(text))]
  in
  let fields =
    match data with None -> fields | Some(d) -> fields @ [("data", d)]
  in
  `Assoc(fields)

let suffix_item_to_yojson
    (Document.{kind; text} : Document.unprocessed_item) =
  let (kind, data) = item_kind_to_yojson kind in
  let fields = [("kind", `String(kind)); ("text", `String(text))] in
  let fields =
    match data with None -> fields | Some(d) -> fields @ [("data", d)]
  in
  `Assoc(fields)

let structured_hyp_to_yojson (h : Rocq_toplevel.structured_hyp) =
  let fields = [("name", `String(h.name))] in
  let fields =
    match h.def with
    | None -> fields
    | Some(defn) -> fields @ [("defn", `String(defn))]
  in
  `Assoc(fields @ [("type", `String(h.hyp_type))])

let structured_goal_to_yojson (g : Rocq_toplevel.structured_goal) =
  let hyps = `List(List.map structured_hyp_to_yojson g.hyps) in
  `Assoc([("hyps", hyps); ("goal", `String(g.goal))])

let document_to_yojson d =
  let prefix =
    let rev_prefix = Document.rev_prefix d in
    `List(List.rev_map prefix_item_to_yojson rev_prefix)
  in
  let suffix =
    let suffix = Document.suffix d in
    `List(List.map suffix_item_to_yojson suffix)
  in
  let goals =
    match Document.structured_goals d with
    | None        -> `Null
    | Some(goals) -> `List(List.map structured_goal_to_yojson goals)
  in
  `Assoc([("prefix", prefix); ("suffix", suffix); ("goals", goals)])

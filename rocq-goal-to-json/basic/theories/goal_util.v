Require skylabs_ai.ltac2_json.JSON.
Import Ltac2 Ltac2.Printf.

Ltac2 goal_to_json (_ : unit) : JSON.t :=
  let to_string c := Message.to_string (fprintf "%t" c) in
  let build_hyp (x, odef, ty) :=
    JSON.Assoc (
      ("name", JSON.String (Message.to_string (Message.of_ident x))) ::
      ("type", JSON.String (to_string ty)) ::
      match odef with
      | None     => []
      | Some def => [("def", JSON.String (to_string def))]
      end
    )
  in
  let goal := Control.goal () in
  JSON.Assoc [
    ("hyps", JSON.List (List.map build_hyp (Control.hyps ())));
    ("goal", JSON.String (to_string goal))].

Ltac goal_to_json :=
  ltac2:(Control.enter (fun _ => printf "%s" (JSON.to_string (goal_to_json ())))).

Require Import iris.proofmode.base.
Require Import iris.proofmode.environments.
Require Import iris.bi.bi.

Require Import bluerock.ltac2.extra.extra.
Require skylabs_ai.ltac2_json.JSON.
Import Ltac2 Control.Notations Ltac2.Printf.

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
  let ipm_goal :=
    let rec get_env acc env :=
      let to_json name p :=
        let of_string s :=
          match String.of_string_constr s with
          | None => user_err! "Ill-formed IPM environment."
          | Some s => s
          end
        in
        let name :=
          lazy_match! name with
          | IAnon _ => JSON.Null
          | INamed ?s => JSON.String (of_string s)
          | _ => user_err! "Ill-formed IPM environment."
          end
        in
        JSON.Assoc [ ("name", name); ("prop", JSON.String (to_string p)) ]
      in
      lazy_match! env with
      | environments.Enil => acc
      | environments.Esnoc ?env ?name ?p =>
          get_env (to_json name p :: acc) env
      | _ => user_err! "Ill-formed IPM environment."
      end
    in
    let rec get_concls acc concls :=
      match concls with
      | [] => List.rev acc
      | concl :: concls =>
          lazy_match! concl with
          | @bi_sep _ ?l ?r => get_concls acc (l :: r :: concls)
          | _ => get_concls (JSON.String (to_string concl) :: acc) concls
          end
      end
    in
    lazy_match! goal with
    | [ |- @environments.envs_entails _
            (@environments.Envs _ ?ctx_p ?ctx_s _) ?concl ] =>
        Some (get_env [] ctx_p, get_env [] ctx_s, get_concls [] [concl])
    | [ |- _ ] =>
        None
    end
  in
  JSON.Assoc (
    ("hyps", JSON.List (List.map build_hyp (Control.hyps ()))) ::
    match ipm_goal with
    | None => [("goal", JSON.String (to_string goal))]
    | Some (ctx_p, ctx_s, concls) =>
        ("pers_hyps", JSON.List ctx_p) ::
        ("spat_hyps", JSON.List ctx_s) ::
        ("concls" , JSON.List concls) :: []
    end
  ).

Ltac goal_to_json :=
  ltac2:(Control.enter (fun _ => printf "%s" (JSON.to_string (goal_to_json ())))).

Require Import iris.proofmode.base.
Require Import iris.proofmode.environments.
Require Import iris.bi.bi.

Require skylabs_ai.ltac2_json.JSON.
Import Ltac2 Ltac2.Printf.

(** This module contains utilities borrowed from the ltac2-extra package found
    in https://github.com/SkyLabsAI/BRiCk/tree/main/ltac2-extra. *)
Module Util.
  (** [of_ascii_constr c] attempts to convert the Coq term [c], intended to be
      a full application of [Ascii] to concrete booleans, into a character. *)
  Ltac2 of_ascii_constr (c : constr) : char option :=
    let bool_to_int (t : constr) : int option :=
      lazy_match! t with
      | true  => Some 1
      | false => Some 0
      | _     => None
      end
    in
    let add xo yo :=
      Option.bind xo (fun x => Option.bind yo (fun y => Some (Int.add x y)))
    in
    let mul2 xo := Option.bind xo (fun x => Some (Int.mul 2 x)) in
    lazy_match! c with
    | Ascii ?b0 ?b1 ?b2 ?b3 ?b4 ?b5 ?b6 ?b7 =>
        let n :=              (bool_to_int b7) in
        let n := add (mul2 n) (bool_to_int b6) in
        let n := add (mul2 n) (bool_to_int b5) in
        let n := add (mul2 n) (bool_to_int b4) in
        let n := add (mul2 n) (bool_to_int b3) in
        let n := add (mul2 n) (bool_to_int b2) in
        let n := add (mul2 n) (bool_to_int b1) in
        let n := add (mul2 n) (bool_to_int b0) in
        Option.bind n (fun n => Some (Char.of_int n))
    | _ => None
    end.

  (** [of_char_list cs] builds a string from the list [cs]. *)
  Ltac2 of_char_list (cs : char list) : string :=
    let len := List.length cs in
    let res := String.make len (Char.of_int 0) in
    List.iteri (String.set res) cs; res.

  (** [of_string_constr t] attempts to build a string from the given Coq term
      [c], which must be a fully concrete and evaluated term of type [string]
      from the [Coq.Strings.String] module. *)
  Ltac2 of_string_constr (t : constr) : string option :=
    let rec build_string acc t :=
      lazy_match! t with
      | String ?c ?t  => Option.bind (of_ascii_constr c)
                           (fun c => build_string (c :: acc) t)
      | EmptyString   => Some (of_char_list (List.rev acc))
      | _             => None
      end
    in
    build_string [] t.
End Util.

Ltac2 Type exn ::= [ Ill_formed_IPM_environment ].

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
          match Util.of_string_constr s with
          | None => Control.throw Ill_formed_IPM_environment
          | Some s => s
          end
        in
        let name :=
          lazy_match! name with
          | IAnon _ => JSON.Null
          | INamed ?s => JSON.String (of_string s)
          | _ => Control.throw Ill_formed_IPM_environment
          end
        in
        JSON.Assoc [ ("name", name); ("prop", JSON.String (to_string p)) ]
      in
      lazy_match! env with
      | environments.Enil => acc
      | environments.Esnoc ?env ?name ?p =>
          get_env (to_json name p :: acc) env
      | _ => Control.throw Ill_formed_IPM_environment
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

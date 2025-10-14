(** Can be removed when we bump to OCaml 5.1 or later. *)
module Array = struct
  include Stdlib.Array

  let find_index : ('a -> bool) -> 'a array -> int option = fun pred a ->
    let exception Found of int in
    try iteri (fun i v -> if pred v then raise (Found(i))) a; None with
    | Found(i) -> Some(i)
end

let split : argv:string array -> string array * string list = fun ~argv ->
  match Array.find_index (String.equal "--") argv with
  | None    -> (argv, [])
  | Some(i) ->
  let prog_args = Array.sub argv 0 i in
  let rocq_args = Array.sub argv (i+1) (Array.length argv - i - 1) in
  (prog_args, Array.to_list rocq_args)

let%test "split_empty" =
  split ~argv:[||] = ([||], [])

let%test "split_no_rocq_args1" =
  split ~argv:[|"a"; "b"; "c"; "d"|] = ([|"a"; "b"; "c"; "d"|], [])

let%test "split_no_rocq_args2" =
  split ~argv:[|"a"; "b"; "c"; "d"; "--"|] = ([|"a"; "b"; "c"; "d"|], [])

let%test "split_only_rocq_args" =
  split ~argv:[|"--"; "a"; "b"; "c"; "d"|] = ([||], ["a"; "b"; "c"; "d"])

let%test "split_both_args" =
  split ~argv:[|"a"; "b"; "--"; "c"; "d"|] = ([|"a"; "b"|], ["c"; "d"])

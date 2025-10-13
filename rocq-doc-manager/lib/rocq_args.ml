let split_at n ls =
  let rec help n ls acc =
    if n = 0 then (List.rev acc, ls)
    else match ls with
        | [] -> (List.rev acc, ls)
        | l :: ls -> help (n - 1) ls (l :: acc)
  in help n ls []

let array_find_index pred ary =
  let rec help n =
    if n >= Array.length ary then None
    else if pred (Array.get ary n) then Some n else help (n + 1)
  in help 0

let get_args : argv:string array -> string array * string list = fun ~argv ->
  match array_find_index (fun x -> x = "--") argv with
  | None -> (argv, [])
  | Some i ->
    let (args, rocq_args) = split_at i (Array.to_list argv) in
    let rocq_args: string list = List.tl rocq_args in
    (Array.of_list args, rocq_args)

let cmp_result exp_args exp_rocq_args (args, rocq_args)  =
  let result =
  Array.length args = Array.length exp_args &&
  Array.for_all2 (fun a b -> a = b) args exp_args &&
  List.length rocq_args = List.length exp_rocq_args &&
  List.for_all2 (fun a b -> a = b) rocq_args exp_rocq_args
  in
  if result then true
  else
  begin
  Array.iter prerr_endline args ;
  List.iter prerr_endline rocq_args ;
  false
  end

let%test "get_args_empty" = cmp_result [||] [] @@ get_args ~argv:[||]
let%test "get_args_only" = cmp_result [|"a"|] ["b"] @@ get_args ~argv:[|"a"; "--"; "b"|]

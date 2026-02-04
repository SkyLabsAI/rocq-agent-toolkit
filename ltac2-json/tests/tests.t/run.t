  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ coqc test.v
  Available derivers: json.
  json_of_variant : variant -> t
  json_of_variant :=
    let rec json_of_variant :=
      fun x =>
      match x with
      | VariantA => variant "VariantA" None
      | VariantB => variant "VariantB" None
      | VariantC => variant "VariantC" None
      end
    in
    json_of_variant
  json_of_point : point -> t
  json_of_point :=
    let rec json_of_point :=
      fun x =>
      Assoc
        [("x", json_of_int x.(x)); ("y", json_of_int x.(y));
          ("z", json_of_int x.(z))]
    in
    json_of_point
  json_of_triple : triple -> t
  json_of_triple :=
    let rec json_of_triple :=
      fun x =>
      match x with
      | (x0, x1, x2) =>
          tuple
            [json_of_list (fun x => json_of_int x) x0; 
              json_of_bool x1; json_of_int x2]
      end
    in
    json_of_triple

  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ coqc test.v
  Available derivers: json.
  variant_to_json : variant -> t
  variant_to_json :=
    fun x =>
    let rec variant_to_json :=
              fun x =>
              match x with
              | VariantA => Variant "VariantA" None
              | VariantB => Variant "VariantB" None
              | VariantC => Variant "VariantC" None
              end
      in
    variant_to_json x
  point_to_json : point -> t
  point_to_json :=
    fun x =>
    let rec point_to_json :=
              fun x =>
              Assoc
                [("x", int_to_json x.(x)); ("y", int_to_json x.(y));
                  ("z", int_to_json x.(z))]
      in
    point_to_json x
  triple_to_json : triple -> t
  triple_to_json :=
    fun x =>
    let rec triple_to_json :=
              fun x =>
              match x with
              | (x0, x1, x2) =>
                  Tuple
                    [list_to_json (fun x => int_to_json x) x0; 
                      bool_to_json x1; int_to_json x2]
              end
      in
    triple_to_json x

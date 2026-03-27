  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ coqc test.v
  [ "Then", [ "Atom", "intros" ], [ "Atom", "intros" ] ]
  [ "Then", [ "Atom", "intro H" ], [ "Atom", "apply _" ] ]
  [
    "Thens",
    [ "Atom", "intro" ],
    [ [ "Atom", "intro" ], [ "Atom", "intros" ], [ "Atom", "apply _" ] ]
  ]
  [ "Solve", [ "Atom", "intro" ], [ "Atom", "apply _" ] ]
  [
    "Thens",
    [ "Atom", "intro" ],
    [ [ "Atom", "intro" ], [ "Atom", "apply _" ] ]
  ]
  [
    "Thens3",
    [ "Atom", "intro" ],
    [],
    [ "Atom", "intro" ],
    [ [ "Atom", "apply _" ] ]
  ]
  [
    "Thens3",
    [ "Atom", "intro" ],
    [],
    [ "Then", [ "Atom", "intro" ], [ "Atom", "apply _" ] ],
    [ [ "Idtac", "idtac" ], [ "Atom", "apply _" ] ]
  ]
  [ "Progress", [ "Atom", "intro" ] ]
  [ "Atom", "match goal with\n| _ => idtac\nend" ]
  [
    "First", [ "Idtac", "idtac" ], [ "Atom", "apply _" ], [ "Atom", "nothing" ]
  ]
  [ "Solve", [ "Idtac", "idtac" ], [ "Atom", "auto" ], [ "Atom", "nothing" ] ]
  [ "Fail", "fail" ]
  [ "Idtac", "idtac \"T\"" ]
  [
    "Then",
    [ "Then", [ "Atom", "intro x" ], [ "Atom", "intro y" ] ],
    [ "Atom", "trivial" ]
  ]
  [ "Then", [ "Atom", "intros" ], [ "Atom", "trivial" ] ]
  [ "Then", [ "Atom", "generalize x" ], [ "Atom", "trivial" ] ]
  [
    "Thens",
    [ "Atom", "assert True" ],
    [ [ "Atom", "trivial" ], [ "Atom", "assumption" ] ]
  ]

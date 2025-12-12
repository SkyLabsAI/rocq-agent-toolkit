  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ cat > commands.txt <<EOF
  > run 0 "Module foo."
  > run 0 "Definition a := nat."
  > run 0 "Module bar."
  > run 0 "Definition b := nat."
  > run 0 "End bar."
  > run 0 "Section junk."
  > run 0 "Definition c := nat."
  > run 0 "End junk."
  > run 0 "End foo."
  > EOF

  $ cat commands.txt | rocq-toplevel-api.tester
  [0] 1 > run 0 "Module foo."
  {
    "feedback_messages": [
      { "level": "info", "text": "Interactive Module foo started" }
    ]
  }
  [0] 2 > run 0 "Definition a := nat."
  {
    "globrefs_diff": { "added_constants": [ "Top.foo.a" ] },
    "feedback_messages": [ { "level": "info", "text": "a is defined" } ]
  }
  [0] 3 > run 0 "Module bar."
  {
    "feedback_messages": [
      { "level": "info", "text": "Interactive Module bar started" }
    ]
  }
  [0] 4 > run 0 "Definition b := nat."
  {
    "globrefs_diff": { "added_constants": [ "Top.foo.bar.b" ] },
    "feedback_messages": [ { "level": "info", "text": "b is defined" } ]
  }
  [0] 5 > run 0 "End bar."
  {
    "feedback_messages": [
      { "level": "info", "text": "Module bar is defined" }
    ]
  }
  [0] 6 > run 0 "Section junk."
  {}
  [0] 7 > run 0 "Definition c := nat."
  {
    "globrefs_diff": { "added_constants": [ "Top.foo.c" ] },
    "feedback_messages": [ { "level": "info", "text": "c is defined" } ]
  }
  [0] 8 > run 0 "End junk."
  {}
  [0] 9 > run 0 "End foo."
  {
    "feedback_messages": [
      { "level": "info", "text": "Module foo is defined" }
    ]
  }
  [0] 10 > [EOF]

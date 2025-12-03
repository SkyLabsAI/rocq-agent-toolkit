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
  {
    "feedback_messages": [
      { "level": "info", "text": "Interactive Module foo started" }
    ]
  }
  OK
  {
    "globrefs_diff": { "added_constants": [ "Top.foo.a" ] },
    "feedback_messages": [ { "level": "info", "text": "a is defined" } ]
  }
  OK
  {
    "feedback_messages": [
      { "level": "info", "text": "Interactive Module bar started" }
    ]
  }
  OK
  {
    "globrefs_diff": { "added_constants": [ "Top.foo.bar.b" ] },
    "feedback_messages": [ { "level": "info", "text": "b is defined" } ]
  }
  OK
  {
    "feedback_messages": [
      { "level": "info", "text": "Module bar is defined" }
    ]
  }
  OK
  {}
  OK
  {
    "globrefs_diff": { "added_constants": [ "Top.foo.c" ] },
    "feedback_messages": [ { "level": "info", "text": "c is defined" } ]
  }
  OK
  {}
  OK
  {
    "feedback_messages": [
      { "level": "info", "text": "Module foo is defined" }
    ]
  }
  OK

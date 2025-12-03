  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ cat > commands.txt <<EOF
  > run 0 "Section test."
  > run 0 "Context (n : nat)."
  > run 0 "Definition get := n."
  > run 0 "End test."
  > run 0 "Check get."
  > EOF

  $ cat commands.txt | rocq-toplevel-api.tester
  {}
  OK
  { "feedback_messages": [ { "level": "info", "text": "n is declared" } ] }
  OK
  {
    "globrefs_diff": { "added_constants": [ "Top.get" ] },
    "feedback_messages": [ { "level": "info", "text": "get is defined" } ]
  }
  OK
  {}
  OK
  {
    "feedback_messages": [
      { "level": "notice", "text": "get\n     : nat -> nat" }
    ]
  }
  OK

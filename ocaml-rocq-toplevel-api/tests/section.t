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
  [0] 1 > run 0 "Section test."
  {}
  [0] 2 > run 0 "Context (n : nat)."
  { "feedback_messages": [ { "level": "info", "text": "n is declared" } ] }
  [0] 3 > run 0 "Definition get := n."
  {
    "globrefs_diff": { "added_constants": [ "Top.get" ] },
    "feedback_messages": [ { "level": "info", "text": "get is defined" } ]
  }
  [0] 4 > run 0 "End test."
  {}
  [0] 5 > run 0 "Check get."
  {
    "feedback_messages": [
      { "level": "notice", "text": "get\n     : nat -> nat" }
    ]
  }
  [0] 6 > [EOF]

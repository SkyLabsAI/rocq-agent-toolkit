  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF

  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF

Negative counts should be rejected by the client without printing the
requested context or goals. The document and daemon remain unaffected.

  $ cat > count.v <<EOF
  > Definition a := 0.
  > Definition b := 1.
  > EOF

  $ eval $(rocq-ed init count.v)
  $ rocq-ed steps --print-context --print-goals --count-items=-1
  Usage: rocq-ed steps [--help] [OPTION]…
  rocq-ed: option '--count-items': expected a non-negative integer or "all"
  [124]
  $ rocq-ed status --context-lines=0
     1| <CURSOR>Definition a := 0.
  $ rocq-ed delete --print-context --print-goals --count-items=-1
  Usage: rocq-ed delete [--help] [OPTION]…
  rocq-ed: option '--count-items': expected a non-negative integer or "all"
  [124]
  $ rocq-ed status --context-lines=0
     1| <CURSOR>Definition a := 0.
  $ rocq-ed status --context-lines=-1 --goals
  Usage: rocq-ed status [--help] [OPTION]…
  rocq-ed: option '--context-lines': expected a non-negative integer, "all", or
           "none"
  [124]
  $ rocq-ed backwards --print-context --print-goals --count-items=-1
  Usage: rocq-ed backwards [--help] [OPTION]…
  rocq-ed: option '--count-items': expected a non-negative integer or "all"
  [124]
  $ rocq-ed status --context-lines=0
     1| <CURSOR>Definition a := 0.

A well-formed command that cannot be applied to the document does print the
requested state.

  $ rocq-ed backwards --print-context=0 --print-goals --count-items=1
  Warning: Only 0 < 1 steps were reverted before reaching the start of the file.
  
     1| <CURSOR>Definition a := 0.
  
  Not currently in a proof.
  $ rocq-ed stop

  $ touch test.v
  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF
  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF

  $ rocq-ed status --session-id xxxxxx
  Error: No active session with ID xxxxxx.
  [123]
  $ eval $(rocq-ed init test.v)
  $ rocq-ed status
     1| <CURSOR>
  $ rocq-ed stop

  $ touch test.v
  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF
  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF

  $ rocq-ed status test.v
  Error: no active session for "test.v".
  [123]
  $ rocq-ed init test.v
  $ rocq-ed status test.v
     1| <CURSOR>
  $ rocq-ed init test.v
  Error: a session is already running for that file.
  [123]
  $ rocq-ed status test.v
     1| <CURSOR>
  $ rocq-ed stop test.v

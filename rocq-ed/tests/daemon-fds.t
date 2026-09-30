  $ touch test.v
  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF
  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF

A daemonized session and its Rocq subprocess must release the output pipe used
by the invoking command. In particular, redirecting stderr to stdout must not
make a downstream process wait for the lifetime of the session.

  $ rocq-ed init test.v 2>&1 | cat > session.env
  $ eval "$(cat session.env)"
  $ rocq-ed status --context-lines 0
     1| <CURSOR>
  $ rocq-ed stop

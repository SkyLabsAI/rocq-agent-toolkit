  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF
  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF
  $ touch test.v

The server's PID means nothing to a client in another PID namespace. Emulate
that with a PID that exists in no namespace.

  $ eval $(rocq-ed init test.v)
  $ echo 2147483647 > "$HOME/.cache/rocq-ed/$ROCQED_SESSION_ID/pid"
  $ rocq-ed status
     1| <CURSOR>
  $ rocq-ed stop
  $ test -d "$HOME/.cache/rocq-ed/$ROCQED_SESSION_ID"
  [1]

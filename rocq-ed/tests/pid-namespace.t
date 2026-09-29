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

A server that died without a stop request gives an error, not a hang.

  $ rocq-ed init --no-daemon test.v > log 2>&1 &
  $ until grep ROCQED_SESSION_ID log > /dev/null; do sleep 0.05; done
  $ export $(grep ROCQED_SESSION_ID log)
  $ kill -KILL %1; wait %1 2> /dev/null
  [137]
  $ rocq-ed status 2>&1 | sed "s/$ROCQED_SESSION_ID/xxxxxx/"; echo "[${PIPESTATUS[0]}]"
  Error: Session with ID xxxxxx is stale or not ready.
  [123]
  $ rocq-ed stop 2>&1 | sed "s/$ROCQED_SESSION_ID/xxxxxx/"; echo "[${PIPESTATUS[0]}]"
  Error: Session with ID xxxxxx is stale or not ready.
  [123]

  $ touch test.v
  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF
  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF

  $ rocq-ed init --no-daemon test.v > log 2>&1 &
  $ server_pid=$!
  $ until grep ROCQED_SESSION_ID log > /dev/null 2>&1; do sleep 0.05; done
  $ export $(grep ROCQED_SESSION_ID log)
  $ rocq-ed status
     1| <CURSOR>

  $ kill ${server_pid}
  $ wait ${server_pid} || true

  $ rocq-ed status 2>&1 | sed "s/$(printenv ROCQED_SESSION_ID)/xxxxxx/"
  Error: session with ID xxxxxx crashed or was killed.
  [123]

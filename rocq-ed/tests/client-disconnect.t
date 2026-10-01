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
  $ until grep ROCQED_SESSION_ID log > /dev/null; do sleep 0.05; done
  $ export $(grep ROCQED_SESSION_ID log)

A client that goes away while its request is being processed must not take the
session down. The request below blocks until its output FIFO is opened, and the
log shows that it was received.

  $ mkfifo block.out
  $ rocq-ed query --text 'Redirect "block" Check I.' > /dev/null 2>&1 &
  $ client_pid=$!
  $ until grep -q block log; do sleep 0.05; done
  $ kill ${client_pid}
  $ wait ${client_pid}
  [143]
  $ exec 3<> block.out

The server drops the response, and keeps serving requests.

  $ rocq-ed status
     1| <CURSOR>
  $ exec 3<&-
  $ grep -c "Failed to send the response" log
  1
  $ rocq-ed stop
  $ wait ${server_pid}

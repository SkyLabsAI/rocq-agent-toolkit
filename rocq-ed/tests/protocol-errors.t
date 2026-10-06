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
  Error: no active session with ID xxxxxx.
  [123]
  $ eval $(rocq-ed init test.v)
  $ rocq-ed status
     1| <CURSOR>

A request made while another one is in progress is rejected. The first request
blocks until its output pipe is opened; the session log shows it was received.

  $ mkfifo block.out
  $ rocq-ed insert --keep=none --text 'Redirect "block" Check I.' > /dev/null 2>&1 &
  $ until grep -q block $HOME/.cache/rocq-ed/$ROCQED_SESSION_ID/log; do sleep 0.05; done
  $ rocq-ed status
  Error: a request is already in progress.
  [123]
  $ exec 3<> block.out
  $ wait $!
  $ exec 3>&-
  $ rocq-ed status
     1| <CURSOR>
  $ rocq-ed stop

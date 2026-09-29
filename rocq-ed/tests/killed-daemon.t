  $ touch test.v
  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF
  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF

  $ eval $(rocq-ed init test.v)
  $ rocq-ed status
     1| <CURSOR>

  $ pid=$(cat $HOME/.cache/rocq-ed/${ROCQED_SESSION_ID}/pid)
  $ kill ${pid}
  $ while kill -0 ${pid} 2>/dev/null; do sleep 0.01; done

  $ rocq-ed status 2>&1 | sed "s/$(printenv ROCQED_SESSION_ID)/xxxxxx/"
  Error: Session with ID xxxxxx crashed or was killed.
  [123]

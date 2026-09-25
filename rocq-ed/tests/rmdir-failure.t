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
  $ touch $HOME/.cache/rocq-ed/$ROCQED_SESSION_ID/extra
  $ rocq-ed stop 2>&1 | sed "s/$ROCQED_SESSION_ID/xxxxxx/"
  Warning: failed to "rmdir $TESTCASE_ROOT/user/.cache/rocq-ed/xxxxxx" (Directory not empty).

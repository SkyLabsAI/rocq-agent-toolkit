  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF

  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF

  $ touch atomic.v succeeding.v all.v
  $ cat > suffix.v <<EOF
  > Definition after := True.
  > EOF

  $ rocq-ed init atomic.v
  $ rocq-ed insert --text "Definition ok := True. Check nope. Definition later := True." atomic.v >/dev/null 2>&1 || true
  $ rocq-ed status --context-lines=0 atomic.v
     1| <CURSOR>
  $ rocq-ed stop atomic.v

  $ rocq-ed init succeeding.v
  $ rocq-ed insert --keep=succeeding --text "Definition ok := True. Check nope. Definition later := True." succeeding.v >/dev/null 2>&1 || true
  $ rocq-ed status --context-lines=0 succeeding.v
     1| Definition ok := True. <CURSOR>
  $ rocq-ed stop succeeding.v

  $ rocq-ed init suffix.v
  $ rocq-ed insert --keep=succeeding --text "Definition ok := True. Check nope. " suffix.v >/dev/null 2>&1 || true
  $ rocq-ed status --context-lines=0 suffix.v
     1| Definition ok := True. <CURSOR>Definition after := True.
  $ rocq-ed stop suffix.v

  $ rocq-ed init all.v
  $ rocq-ed insert --keep=all --text "Definition ok := True. Check nope. Definition later := True." all.v >/dev/null 2>&1 || true
  $ rocq-ed status --context-lines=0 all.v
     1| Definition ok := True. <CURSOR>Check nope. Definition later := True.
  $ rocq-ed stop all.v

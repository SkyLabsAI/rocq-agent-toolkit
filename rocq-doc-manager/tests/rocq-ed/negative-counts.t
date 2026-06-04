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

Negative counts should be rejected without changing the document, and the
daemon should remain responsive afterwards.

  $ cat > count.v <<EOF
  > Definition a := 0.
  > Definition b := 1.
  > EOF

  $ rocq-ed init count.v
  $ rocq-ed steps --count-items=-1 count.v
  Failed after processing 0 items.
  Error: negative count.
  [1]
  $ rocq-ed status --context-lines=0 count.v
     1| <CURSOR>Definition a := 0.
  $ rocq-ed delete --count-items=-1 count.v
  Error: negative count.
  [1]
  $ rocq-ed status --context-lines=0 count.v
     1| <CURSOR>Definition a := 0.
  $ rocq-ed status --context-lines=0 count.v
     1| <CURSOR>Definition a := 0.

`backwards` currently lets negative counts reach the daemon as an uncaught
Invalid_argument exception.  The timeout makes the regression visible without
letting the test suite hang.

  $ timeout 5s rocq-ed backwards --count-items=-1 count.v
  Error: negative count.
  [1]
  $ timeout 5s rocq-ed status --context-lines=0 count.v
     1| <CURSOR>Definition a := 0.
  $ rocq-ed stop count.v >/dev/null 2>&1 || true

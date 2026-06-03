  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ cat > test.v <<EOF
  > Definition x := True.
  > Definition y := x.
  > EOF

  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF

  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF

  $ rocq-ed init test.v
  $ rocq-ed steps --count-items=all test.v
  $ rocq-ed status --context-lines=0 test.v
     3| <CURSOR>
  $ rocq-ed backwards --print-context=0 --count-items=1 test.v
     2| Definition y := x.<CURSOR>
  $ rocq-ed stop test.v

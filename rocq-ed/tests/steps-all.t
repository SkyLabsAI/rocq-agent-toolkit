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

  $ eval $(rocq-ed init test.v)
  $ rocq-ed steps --count-items=all
  $ rocq-ed status --context-lines=0
     3| <CURSOR>
  $ rocq-ed backwards --print-context=0 --count-items=1
     2| Definition y := x.<CURSOR>
  $ rocq-ed stop

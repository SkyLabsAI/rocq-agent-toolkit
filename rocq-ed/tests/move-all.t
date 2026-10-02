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
  $ rocq-ed move --item=100
  Error: index out of bounds.
  [1]
  $ rocq-ed status --context-lines=0
     1| <CURSOR>Definition x := True.
  $ rocq-ed move --item=+all
  $ rocq-ed status --context-lines=0
     3| <CURSOR>
  $ rocq-ed move --print-context=0 --item=-1
     2| Definition y := x.<CURSOR>
  $ rocq-ed move --print-context=0 --item=1
     1| Definition x := True.<CURSOR>
  $ rocq-ed move --print-context=0 --item=3
     2| Definition y := x.<CURSOR>
  $ rocq-ed move --item=-all
  $ rocq-ed status --context-lines=0
     1| <CURSOR>Definition x := True.
  $ rocq-ed stop

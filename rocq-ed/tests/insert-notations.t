  $ cat > test.v <<EOF
  > Notation "x '+++' y" := (x + y) (at level 50, left associativity).
  > EOF

  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF

  $ cat > dune <<EOF
  > (rocq.theory
  >  (name test))
  > EOF

  $ eval $(rocq-ed init test.v)
  $ rocq-ed move --item=+all
  $ rocq-ed insert --text=" Check 1 +++ 2. Notation \"'zz'\" := 3. Check zz."
  1 +++ 2
       : nat
  3
       : nat
  $ rocq-ed stop

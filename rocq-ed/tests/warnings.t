Warnings emitted while processing commands are printed on insert and steps.

  $ cat > test.v <<EOF
  > #[deprecated(since="1.0", note="use bar")] Definition foo := 0.
  > Definition x := 1.
  > Definition y := 2.
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
  $ rocq-ed steps --count-items 1
  $ rocq-ed insert --text $'\nCheck foo.\n'
  Warning: Reference foo is deprecated since 1.0. use bar
  [deprecated-reference-since-1.0,deprecated-since-1.0,deprecated-reference,deprecated,default]
  foo
       : nat

Re-processing items prints their warnings again.

  $ rocq-ed backwards --count-items 3
  $ rocq-ed steps --count-items all
  Warning: Reference foo is deprecated since 1.0. use bar
  [deprecated-reference-since-1.0,deprecated-since-1.0,deprecated-reference,deprecated,default]
  foo
       : nat
  $ rocq-ed stop

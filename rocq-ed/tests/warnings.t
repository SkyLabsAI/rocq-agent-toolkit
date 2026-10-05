Warnings emitted while processing commands are printed on insert and move.

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
  $ rocq-ed move --feedback=+info --item=+1
  foo is defined
  $ rocq-ed insert --text $'\nCheck foo.\n'
  Warning: Reference foo is deprecated since 1.0. use bar
  [deprecated-reference-since-1.0,deprecated-since-1.0,deprecated-reference,deprecated,default]
  foo
       : nat

Re-processing items prints their warnings again.

  $ rocq-ed move --item=-3
  $ rocq-ed move --item=+all
  Warning: Reference foo is deprecated since 1.0. use bar
  [deprecated-reference-since-1.0,deprecated-since-1.0,deprecated-reference,deprecated,default]
  foo
       : nat

Feedback levels can be enabled and disabled relative to the default. Notices
remain enabled in this example, but the warning is disabled.

  $ rocq-ed insert --keep=none --feedback=+info,-warning --text $'\nDefinition modified := 3.\nCheck foo.\n'
  modified is defined
  foo
       : nat

An unsigned list enables exactly the listed feedback levels.

  $ rocq-ed insert --keep=none --feedback=debug,info --text $'\nSet Debug "vernacinterp".\nDefinition explicit := 5.\nCheck foo.\n'
  Debug: [vernacinterp] interpreting: Definition explicit := 5
  explicit is defined
  Debug: [vernacinterp] interpreting: Check foo

The default levels can also be selected explicitly.

  $ rocq-ed insert --keep=none --feedback=notice,warning --text $'\nCheck foo.\n'
  Warning: Reference foo is deprecated since 1.0. use bar
  [deprecated-reference-since-1.0,deprecated-since-1.0,deprecated-reference,deprecated,default]
  foo
       : nat

All feedback can be disabled.

  $ rocq-ed insert --keep=none --feedback=none --text $'\nCheck foo.\n'

Or enabled, including informational messages.

  $ rocq-ed insert --keep=none --feedback=all --text $'\nDefinition all_info := 4.\nCheck foo.\n'
  all_info is defined
  Warning: Reference foo is deprecated since 1.0. use bar
  [deprecated-reference-since-1.0,deprecated-since-1.0,deprecated-reference,deprecated,default]
  foo
       : nat

Debug feedback is retained and can be printed too.

  $ rocq-ed insert --keep=none --feedback=+debug --text $'\nSet Debug "vernacinterp".\nDefinition debugged := 5.\n'
  Debug: [vernacinterp] interpreting: Definition debugged := 5

Error feedback is handled separately and is not configurable.

  $ rocq-ed move --item=+1 --feedback=+error 2>&1 | grep -o 'invalid feedback selector "+error"'
  invalid feedback selector "+error"
  [124]
  $ rocq-ed stop

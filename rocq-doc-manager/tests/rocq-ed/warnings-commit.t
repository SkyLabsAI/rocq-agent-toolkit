Warnings emitted while processing commands are printed on insert and steps,
and commit reports unprocessed items (or excludes them).

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

  $ rocq-ed init test.v
  $ rocq-ed steps --count-items 1 test.v
  $ rocq-ed insert --text $'\nCheck foo.\n' test.v
  Warning: Reference foo is deprecated since 1.0. use bar
  [deprecated-reference-since-1.0,deprecated-since-1.0,deprecated-reference,deprecated,default]

A prefix edit leaves the suffix unprocessed; a plain commit writes it and says so.

  $ rocq-ed backwards --count-items 1 test.v
  $ rocq-ed commit test.v
  Warning: 2 unprocessed item(s) after the cursor were written without having been checked by Rocq.
  $ cat test.v
  #[deprecated(since="1.0", note="use bar")] Definition foo := 0.
  Check foo.
  
  Definition x := 1.
  Definition y := 2.

--exclude-suffix writes only the processed prefix, to a snapshot with --file.

  $ rocq-ed commit --exclude-suffix --file snapshot.v test.v
  $ cat snapshot.v; echo
  #[deprecated(since="1.0", note="use bar")] Definition foo := 0.
  Check foo.

Re-processing items prints their warnings again.

  $ rocq-ed backwards --count-items 2 test.v
  $ rocq-ed steps --count-items all test.v
  Warning: Reference foo is deprecated since 1.0. use bar
  [deprecated-reference-since-1.0,deprecated-since-1.0,deprecated-reference,deprecated,default]
  $ rocq-ed stop test.v

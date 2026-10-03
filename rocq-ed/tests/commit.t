Test commit behaviour.

  $ cat > test.v <<EOF
  > Definition x := 0.
  > Definition y := 1.
  > Definition z := 2.
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
  $ rocq-ed move --item=+2

Check that committing fails by default if there are unprocessed items.

  $ rocq-ed commit --file partial.v
  Error: unable to commit.
  The document is not fully processed (non-empty suffix).
  [1]

Check that committing excludes the unprocessed suffix.

  $ rocq-ed commit --file partial.v --force
  $ cat partial.v
  Definition x := 0.

We can explicitly include the suffix with --include-suffix.

  $ rocq-ed commit --include-suffix --file full.v
  $ diff full.v test.v

We can also commit to the original file.

  $ rocq-ed commit --force
  $ cat test.v
  Definition x := 0.

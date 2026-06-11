  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ cat > test.v <<EOF
  > EOF

  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF

  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF

  $ timeout 5s rocq-ed init test.v
  $ timeout 5s rocq-ed steps --count-items=all test.v
  $ timeout 5s rocq-ed insert --print-context --text="Goal True. Proof. *" test.v
     1| Goal True. Proof. *<CURSOR>

  $ timeout 5s rocq-ed insert --text="*idtac" test.v
  Error: could not process suffix "*idtac".
  inserted text would change the command before the cursor
  The document is unchanged.
  [1]

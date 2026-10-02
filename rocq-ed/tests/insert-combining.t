  $ touch test.v

  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF

  $ cat > dune <<EOF
  > (rocq.theory
  >  (name test))
  > EOF

  $ eval $(rocq-ed init test.v)
  $ rocq-ed steps --count-items=all
  $ rocq-ed insert --print-context --text="Goal True. Proof. *"
     1| Goal True. Proof. *<CURSOR>

  $ rocq-ed insert --text="*idtac"
  The document is unchanged.
  
  Error: could not process suffix "*idtac".
  inserted text would change the command before the cursor
  [1]

  $ rocq-ed stop

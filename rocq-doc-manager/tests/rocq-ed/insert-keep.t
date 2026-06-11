  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled

  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF

  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF

  $ touch atomic.v successful.v all.v parse_fail.v
  $ cat > suffix.v <<EOF
  > Definition after := True.
  > EOF

Atomic insertions report the failing suffix, exit with failure, and leave the
document unchanged.

  $ rocq-ed init atomic.v
  $ sh -c 'rocq-ed insert --print-context --print-goals --text "Definition ok := True. Check nope. Definition later := True." atomic.v >out 2>&1; code=$?; grep -F "Error: could not process suffix \"Check nope. Definition later := True.\"." out; grep -F "The document is unchanged." out; echo "EXIT:$code"'
  Error: could not process suffix "Check nope. Definition later := True.".
  The document is unchanged.
  EXIT:1
  $ rocq-ed status --context-lines=0 atomic.v
     1| <CURSOR>
  $ rocq-ed stop atomic.v

With --keep=successful, successfully processed items are kept, but the failing
and later inserted items are discarded.

  $ rocq-ed init successful.v
  $ sh -c 'rocq-ed insert --print-context --print-goals --keep=successful --text "Definition ok := True. Check nope. Definition later := True." successful.v >out 2>&1; code=$?; grep -F "Error: could not process suffix \"Check nope. Definition later := True.\"." out; if grep -q "The document is unchanged." out; then echo "unexpected unchanged message"; fi; echo "EXIT:$code"'
  Error: could not process suffix "Check nope. Definition later := True.".
  EXIT:1
  $ rocq-ed status --context-lines=0 successful.v
     1| Definition ok := True. <CURSOR>
  $ rocq-ed stop successful.v

The original suffix is preserved when discarding inserted suffix items.

  $ rocq-ed init suffix.v
  $ sh -c 'rocq-ed insert --print-context --print-goals --keep=successful --text "Definition ok := True. Check nope. " suffix.v >out 2>&1; code=$?; grep -F "Error: could not process suffix \"Check nope. \"." out; if grep -q "The document is unchanged." out; then echo "unexpected unchanged message"; fi; echo "EXIT:$code"'
  Error: could not process suffix "Check nope. ".
  EXIT:1
  $ rocq-ed status --context-lines=0 suffix.v
     1| Definition ok := True. <CURSOR>Definition after := True.
  $ rocq-ed stop suffix.v

With --keep=all, the failing and later inserted items remain in the suffix.

  $ rocq-ed init all.v
  $ sh -c 'rocq-ed insert --print-context --print-goals --keep=all --text "Definition ok := True. Check nope. Definition later := True." all.v >out 2>&1; code=$?; grep -F "Error: could not process suffix \"Check nope. Definition later := True.\"." out; if grep -q "The document is unchanged." out; then echo "unexpected unchanged message"; fi; echo "EXIT:$code"'
  Error: could not process suffix "Check nope. Definition later := True.".
  EXIT:1
  $ rocq-ed status --context-lines=0 all.v
     1| Definition ok := True. <CURSOR>Check nope. Definition later := True.
  $ rocq-ed stop all.v

Parse failures are still atomic even with --keep=all, because no reliable item
boundary was found to insert into the document.

  $ rocq-ed init parse_fail.v
  $ sh -c 'rocq-ed insert --print-context --print-goals --keep=all --text "(* unterminated" parse_fail.v >out 2>&1; code=$?; grep -F "Error: could not process suffix \"(* unterminated\"." out; grep -F "unclosed initial comment" out; grep -F "The document is unchanged." out; echo "EXIT:$code"'
  Error: could not process suffix "(* unterminated".
  unclosed initial comment
  The document is unchanged.
  EXIT:1
  $ rocq-ed status --context-lines=0 parse_fail.v
     1| <CURSOR>
  $ rocq-ed stop parse_fail.v

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

Atomic insertions report the remaining inserted text, exit with failure, and
leave the document unchanged. This is the default, and --keep=atomic selects
it explicitly. A successful atomic insertion is kept.

  $ eval $(rocq-ed init atomic.v)
  $ sh -c 'rocq-ed insert --print-context --print-goals --text "Definition ok := True. Check nope. Definition later := True." >out 2>&1; code=$?; grep -F "Error: could not parse or process remaining text \"Check nope. Definition later := True.\"." out; grep -F "The document is unchanged." out; echo "EXIT:$code"'
  Error: could not parse or process remaining text "Check nope. Definition later := True.".
  The document is unchanged.
  EXIT:1
  $ rocq-ed insert --keep=atomic --text "Definition ok := True. Check nope." > /dev/null 2>&1
  [1]
  $ rocq-ed status --context-lines=0
     1| <CURSOR>
  $ rocq-ed insert --keep=atomic --text "Definition ok := True."
  $ rocq-ed status --context-lines=0
     1| Definition ok := True.<CURSOR>
  $ rocq-ed stop

With --keep=successful, successfully processed items are kept, but the failing
and later inserted items are discarded.

  $ eval $(rocq-ed init successful.v)
  $ sh -c 'rocq-ed insert --print-context --print-goals --keep=successful --text "Definition ok := True. Check nope. Definition later := True." >out 2>&1; code=$?; grep -F "Error: could not parse or process remaining text \"Check nope. Definition later := True.\"." out; if grep -q "The document is unchanged." out; then echo "unexpected unchanged message"; fi; echo "EXIT:$code"'
  Error: could not parse or process remaining text "Check nope. Definition later := True.".
  EXIT:1
  $ rocq-ed status --context-lines=0
     1| Definition ok := True. <CURSOR>
  $ rocq-ed stop

The original suffix is preserved when discarding inserted suffix items.

  $ eval $(rocq-ed init suffix.v)
  $ sh -c 'rocq-ed insert --print-context --print-goals --keep=successful --text "Definition ok := True. Check nope. " >out 2>&1; code=$?; grep -F "Error: could not parse or process remaining text \"Check nope. \"." out; if grep -q "The document is unchanged." out; then echo "unexpected unchanged message"; fi; echo "EXIT:$code"'
  Error: could not parse or process remaining text "Check nope. ".
  EXIT:1
  $ rocq-ed status --context-lines=0
     1| Definition ok := True. <CURSOR>Definition after := True.
  $ rocq-ed stop

With --keep=all, the failing and later inserted items remain in the suffix.

  $ eval $(rocq-ed init all.v)
  $ sh -c 'rocq-ed insert --print-context --print-goals --keep=all --text "Definition ok := True. Check nope. Definition later := True." >out 2>&1; code=$?; grep -F "Error: could not parse or process remaining text \"Check nope. Definition later := True.\"." out; if grep -q "The document is unchanged." out; then echo "unexpected unchanged message"; fi; echo "EXIT:$code"'
  Error: could not parse or process remaining text "Check nope. Definition later := True.".
  EXIT:1
  $ rocq-ed status --context-lines=0
     1| Definition ok := True. <CURSOR>Check nope. Definition later := True.
  $ rocq-ed stop

Parse failures are still atomic even with --keep=all, because no reliable item
boundary was found to insert into the document.

  $ eval $(rocq-ed init parse_fail.v)
  $ sh -c 'rocq-ed insert --print-context --print-goals --keep=all --text "(* unterminated" >out 2>&1; code=$?; grep -F "Error: could not parse or process remaining text \"(* unterminated\"." out; grep -F "unclosed initial comment" out; grep -F "The document is unchanged." out; echo "EXIT:$code"'
  Error: could not parse or process remaining text "(* unterminated".
  unclosed initial comment
  The document is unchanged.
  EXIT:1
  $ rocq-ed status --context-lines=0
     1| <CURSOR>
  $ rocq-ed stop

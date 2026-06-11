  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ export TERM=dumb

  $ rocq-ed init test.v

`goto-section` moves to the `Section` command introducing the named section.

  $ rocq-ed goto-section Outer test.v >/dev/null
  $ rocq-ed status -C 0 test.v
     3| <CURSOR>Section Outer.

`section-end` moves to the matching `End` command, using nesting to avoid
stopping at an inner section end.

  $ rocq-ed section-end Outer test.v >/dev/null
  $ rocq-ed status -C 0 test.v
    25| <CURSOR>End Outer.
  $ rocq-ed section-end Inner test.v >/dev/null
  $ rocq-ed status -C 0 test.v
    19|   <CURSOR>End Inner.

`goto-lemma` matches theorem-style declarations regardless of their keyword.

  $ rocq-ed goto-lemma first test.v >/dev/null
  $ rocq-ed status -C 0 test.v
     6|   <CURSOR>Lemma first : True.
  $ rocq-ed goto-lemma second test.v >/dev/null
  $ rocq-ed status -C 0 test.v
    11|   <CURSOR>Theorem second : n = n.
  $ rocq-ed goto-lemma inside test.v >/dev/null
  $ rocq-ed status -C 0 test.v
    17|     <CURSOR>Remark inside : True.
  $ rocq-ed goto-lemma later test.v >/dev/null
  $ rocq-ed status -C 0 test.v
    21|   <CURSOR>Corollary later : True.
  $ rocq-ed goto-lemma after_section test.v >/dev/null
  $ rocq-ed status -C 0 test.v
    27| <CURSOR>Fact after_section : True.

Named navigation can also jump backwards to an item whose index is already in
the processed prefix.

  $ rocq-ed goto-lemma first test.v >/dev/null
  $ rocq-ed status -C 0 test.v
     6|   <CURSOR>Lemma first : True.

`lemma-end` moves to the final command belonging to the declaration/proof.
For a standard proof that command is `Qed.`; this also works when the proof is
written on one line.

  $ rocq-ed lemma-end second test.v >/dev/null
  $ rocq-ed status -C 0 test.v
    14|   <CURSOR>Qed.
  $ rocq-ed lemma-end inside test.v >/dev/null
  $ rocq-ed status -C 0 test.v
    18|     Proof. exact I. <CURSOR>Qed.

`next-lemma` searches forward from the current cursor. When the cursor is at a
lemma declaration, the current lemma is skipped.

  $ rocq-ed goto --pos 1:1 test.v >/dev/null
  $ rocq-ed next-lemma test.v >/dev/null
  $ rocq-ed status -C 0 test.v
     6|   <CURSOR>Lemma first : True.
  $ rocq-ed next-lemma test.v >/dev/null
  $ rocq-ed status -C 0 test.v
    11|   <CURSOR>Theorem second : n = n.
  $ rocq-ed lemma-end second test.v >/dev/null
  $ rocq-ed next-lemma test.v >/dev/null
  $ rocq-ed status -C 0 test.v
    17|     <CURSOR>Remark inside : True.

  $ rocq-ed stop test.v

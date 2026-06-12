  $ export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
  $ export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
  $ export DUNE_CACHE=disabled
  $ rocq-ed init test.v

`goto-section` moves to the `Section` command introducing the named section.

  $ rocq-ed goto-section Outer test.v
     1| (* Prelude. *)
     2| 
     3| <CURSOR>Section Outer.
     4|   Variable n : nat.
     5| 
     6|   Lemma first : True.
     7|   Proof.
     8|     exact I.
  
  Not currently in a proof.
  $ rocq-ed status -C 0 test.v
     3| <CURSOR>Section Outer.

`section-end` moves to the matching `End` command, using nesting to avoid
stopping at an inner section end.

  $ rocq-ed section-end Outer test.v
    20| 
    21|   Corollary later : True.
    22|   Proof.
    23|     exact I.
    24|   Qed.
    25| <CURSOR>End Outer.
    26| 
    27| Fact after_section : True.
    28| Proof.
    29|   exact I.
    30| Qed.
  
  Not currently in a proof.
  $ rocq-ed status -C 0 test.v
    25| <CURSOR>End Outer.
  $ rocq-ed section-end Inner test.v
    14|   Qed.
    15| 
    16|   Section Inner.
    17|     Remark inside : True.
    18|     Proof. exact I. Qed.
    19|   <CURSOR>End Inner.
    20| 
    21|   Corollary later : True.
    22|   Proof.
    23|     exact I.
    24|   Qed.
  
  Not currently in a proof.
  $ rocq-ed status -C 0 test.v
    19|   <CURSOR>End Inner.

`goto-lemma` matches theorem-style declarations regardless of their keyword.

Named navigation can also jump backwards to an item whose index is already in
the processed prefix.

  $ rocq-ed goto-lemma first test.v
     1| (* Prelude. *)
     2| 
     3| Section Outer.
     4|   Variable n : nat.
     5| 
     6|   <CURSOR>Lemma first : True.
     7|   Proof.
     8|     exact I.
     9|   Qed.
    10| 
    11|   Theorem second : n = n.
  
  Not currently in a proof.
  $ rocq-ed status -C 0 test.v
     6|   <CURSOR>Lemma first : True.

`lemma-end` moves to the final command belonging to the declaration/proof.
For a standard proof that command is `Qed.`; this also works when the proof is
written on one line.

  $ rocq-ed lemma-end second test.v
     9|   Qed.
    10| 
    11|   Theorem second : n = n.
    12|   Proof.
    13|     reflexivity.
    14|   <CURSOR>Qed.
    15| 
    16|   Section Inner.
    17|     Remark inside : True.
    18|     Proof. exact I. Qed.
    19|   End Inner.
  
  $ rocq-ed status -C 0 test.v
    14|   <CURSOR>Qed.
  $ rocq-ed lemma-end inside test.v
    13|     reflexivity.
    14|   Qed.
    15| 
    16|   Section Inner.
    17|     Remark inside : True.
    18|     Proof. exact I. <CURSOR>Qed.
    19|   End Inner.
    20| 
    21|   Corollary later : True.
    22|   Proof.
    23|     exact I.
  
  $ rocq-ed status -C 0 test.v
    18|     Proof. exact I. <CURSOR>Qed.

`next-lemma` searches forward from the current cursor. When the cursor is at a
lemma declaration, the current lemma is skipped.

  $ rocq-ed goto --pos 1:1 test.v
     1| <CURSOR>(* Prelude. *)
     2| 
     3| Section Outer.
     4|   Variable n : nat.
     5| 
     6|   Lemma first : True.
  
  Not currently in a proof.
  $ rocq-ed next-lemma test.v
     1| (* Prelude. *)
     2| 
     3| Section Outer.
     4|   Variable n : nat.
     5| 
     6|   <CURSOR>Lemma first : True.
     7|   Proof.
     8|     exact I.
     9|   Qed.
    10| 
    11|   Theorem second : n = n.
  
  Not currently in a proof.
  $ rocq-ed status -C 0 test.v
     6|   <CURSOR>Lemma first : True.
  $ rocq-ed next-lemma test.v
     6|   Lemma first : True.
     7|   Proof.
     8|     exact I.
     9|   Qed.
    10| 
    11|   <CURSOR>Theorem second : n = n.
    12|   Proof.
    13|     reflexivity.
    14|   Qed.
    15| 
    16|   Section Inner.
  
  Not currently in a proof.
  $ rocq-ed status -C 0 test.v
    11|   <CURSOR>Theorem second : n = n.
  $ rocq-ed lemma-end second test.v
     9|   Qed.
    10| 
    11|   Theorem second : n = n.
    12|   Proof.
    13|     reflexivity.
    14|   <CURSOR>Qed.
    15| 
    16|   Section Inner.
    17|     Remark inside : True.
    18|     Proof. exact I. Qed.
    19|   End Inner.
  
  $ rocq-ed next-lemma test.v
    12|   Proof.
    13|     reflexivity.
    14|   Qed.
    15| 
    16|   Section Inner.
    17|     <CURSOR>Remark inside : True.
    18|     Proof. exact I. Qed.
    19|   End Inner.
    20| 
    21|   Corollary later : True.
    22|   Proof.
  
  Not currently in a proof.
  $ rocq-ed status -C 0 test.v
    17|     <CURSOR>Remark inside : True.

`next-section` searches forward from the current cursor. When the cursor is at a
`Section` keyword, the current section is skipped.

  $ rocq-ed goto --pos 1:1 test.v
     1| <CURSOR>(* Prelude. *)
     2| 
     3| Section Outer.
     4|   Variable n : nat.
     5| 
     6|   Lemma first : True.
  
  Not currently in a proof.
  $ rocq-ed next-section test.v
     1| (* Prelude. *)
     2| 
     3| <CURSOR>Section Outer.
     4|   Variable n : nat.
     5| 
     6|   Lemma first : True.
     7|   Proof.
     8|     exact I.
  
  Not currently in a proof.
  $ rocq-ed status -C 0 test.v
     3| <CURSOR>Section Outer.
  $ rocq-ed next-section test.v
    11|   Theorem second : n = n.
    12|   Proof.
    13|     reflexivity.
    14|   Qed.
    15| 
    16|   <CURSOR>Section Inner.
    17|     Remark inside : True.
    18|     Proof. exact I. Qed.
    19|   End Inner.
    20| 
    21|   Corollary later : True.
  
  Not currently in a proof.
  $ rocq-ed status -C 0 test.v
    16|   <CURSOR>Section Inner.
  $ rocq-ed section-end second test.v
  Error: no section named "second".
  The cursor is now at index 21.
  [1]
  $ rocq-ed next-section test.v
  Error: no next section.
  The cursor is now at index 21.
  [1]
  $ rocq-ed status -C 0 test.v
    16|   <CURSOR>Section Inner.

  $ rocq-ed stop test.v

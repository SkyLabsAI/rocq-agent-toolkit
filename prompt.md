
Context:
 - in fmdeps/rocq-agent-toolkit/rocq-doc-manager/lib is the ml implementation of a document manager
 - the document manager is used by `rocq-ed` which is implemented here `rocq-agent-toolkit/rocq-doc-manager/bin/rocq-ed`

Goal:
 - implement the following user commands:
   - goto-lemma NAME: move the cursor to a lemma named `NAME`, whether it be declared as a lemma, theorem, etc.
   - lemma-end NAME: go to the last command that is a part of the lemma declaration or its proof
   - next-lemma: jump to the next lemma
   - goto-section NAME: move cursor to the beginning of a section named `NAME`
   - section-end NAME:  move cursor to the end of the section `NAME`
 - make the necessary changes in the document manager

Output:
   - a number of test cases demonstrating the purpose of the commands listed above
   - file `proposal.md`:
     - a plan for changing the document manager to allow the implementation of above commands
     - a plan for implementing the commands in `rocq-ed`

Limitations:
  - the only files that can be written to disk are `proposal.md` and the test cases produced for `rocq-ed`

References:
- https://github.com/SkyLabsAI/rocq-agent-toolkit/blob/51ae58becd23c2c89decef5de2a63d6a862b4e0b/rocq-doc-manager/lib/document.mli#L85
- https://github.com/SkyLabsAI/rocq-agent-toolkit/blob/51ae58becd23c2c89decef5de2a63d6a862b4e0b/ocaml-rocq-simple-api/lib/api/rocq_vernac_entry.mli#L28
- https://github.com/SkyLabsAI/rocq/blob/bef7df542ab174b83b2f25c3378fe7ef8d9dba59/vernac/vernacexpr.mli#L404-L521

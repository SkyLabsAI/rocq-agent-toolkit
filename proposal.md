# Proposal: named navigation for `rocq-ed`

## Semantics to implement

- `goto-lemma NAME FILE`: move the cursor to the command that starts the first theorem-style declaration whose declared id is exactly `NAME` (`Lemma`, `Theorem`, `Fact`, `Remark`, `Property`, `Proposition`, `Corollary`).
- `lemma-end NAME FILE`: move the cursor to the final command belonging to that declaration/proof, normally `Qed.`, `Defined.`, or `Admitted.`. The cursor is placed before that final command, matching the existing item-index navigation model.
- `next-lemma FILE`: move to the first theorem-style declaration whose start item is strictly after the current cursor index.
- `goto-section NAME FILE`: move to the `Section NAME.` command.
- `section-end NAME FILE`: move to the matching `End NAME.` command, respecting nested sections/modules.

All commands should use exact unqualified names, skip commands wrapped in `Fail`/`Succeed`, and use the existing `with_auto_print` behavior used by `goto`.

## Document manager changes

1. Add semantic navigation helpers to `rocq-doc-manager/lib/document.{mli,ml}`.

   Proposed public data types:

   ```ocaml
   type lemma_kind =
     [ `Theorem | `Lemma | `Fact | `Remark | `Property
     | `Proposition | `Corollary ]

   type lemma_span = {
     name : string;
     names : string list;      (* all names declared by the start command *)
     kind : lemma_kind;
     start_index : int;        (* declaration command *)
     end_index : int option;   (* final proof command, if found *)
   }

   type section_span = {
     name : string;
     start_index : int;        (* Section command *)
     end_index : int option;   (* matching End command *)
   }

   val lemma_spans : t -> lemma_span list
   val section_spans : t -> section_span list
   val find_lemma : t -> name:string -> lemma_span option
   val find_next_lemma : t -> lemma_span option
   val find_section : t -> name:string -> section_span option
   ```

2. Internally, scan `List.rev (rev_prefix d) @ suffix d` with stable document indices. Reuse each processed item index and compute suffix indices from `cursor_index d`.

3. Identify lemma starts by pattern-matching the attached vernacular AST:

   ```ocaml
   match snd command.CAst.v with
   | Vernacexpr.VernacSynPure
       (Vernacexpr.VernacStartTheoremProof (kind, proof_exprs)) -> ...
   | _ -> None
   ```

   Extract ids from `proof_exprs`. Map `Decls.theorem_kind` to `lemma_kind`. Ignore `ControlFail` and `ControlSucceed`.

4. Compute `lemma_span.end_index` by scanning forward from the start command until the first proof-closing command:

   - `VernacSynPure (VernacEndProof _)` for `Qed.`, `Defined.`, and `Admitted.`
   - optionally `VernacSynPure (VernacExactProof _)` if the current Rocq parser uses it for proof-term closure
   - optionally `VernacAbort` as an error/aborted end marker, not as a successfully declared lemma

5. Identify sections by maintaining a segment stack:

   - push `EVernacBeginSection id` as a section segment;
   - push interactive modules/module types too, so their `End` commands do not accidentally close sections;
   - pop on `EVernacEndSegment id` and record the end index when the popped segment is a section.

   This is necessary because `EVernacEndSegment` only carries the name; it does not by itself say whether the `End` closes a section or a module.

6. Keep the helpers pure with respect to Rocq execution: they should only inspect the current in-memory document and never advance/revert the cursor. Movement remains the responsibility of `Document.go_to`.

7. If the JSON-RPC document-manager API should expose the same functionality, add read-only methods returning the spans above, plus optional movement methods that call `Document.go_to` on the selected index.

## `rocq-ed` implementation plan

1. Extend `bin/rocq-ed/request.ml` with request constructors:

   ```ocaml
   | GotoLemma : {name : string} -> (unit, int) t
   | LemmaEnd : {name : string} -> (unit, int) t
   | NextLemma : (unit, int) t
   | GotoSection : {name : string} -> (unit, int) t
   | SectionEnd : {name : string} -> (unit, int) t
   | NextSectionOrEnd : {name : string} -> (unit, int) t
   ```

   The error payload should be the current cursor index, like `Goto`.

2. Add request runners:

   - find the target span using the new `Document` helper;
   - choose `start_index` for `goto-lemma`, `next-lemma`, and `goto-section`;
   - choose `end_index` for `lemma-end` and `section-end`;
   - call `Document.go_to d ~index`;
   - return clear errors for missing names, missing proof ends, missing section ends, or execution failures while advancing.

3. In `bin/rocq-ed/main.ml`, add Cmdliner commands:

   - `goto-lemma NAME FILE`
   - `lemma-end NAME FILE`
   - `next-lemma FILE`
   - `goto-section NAME FILE`
   - `section-end NAME FILE`

   Existing `rocq_file` is positional argument 0, so named commands need a helper for `FILE` at positional argument 1 while `NAME` occupies positional argument 0.

4. Register the new commands in the top-level command list and use `with_auto_print` for all movement commands.

## Tests added

Added cram tests in:

- `fmdeps/rocq-agent-toolkit/rocq-doc-manager/tests/rocq-ed/named-navigation.t`

The tests specify:

- nested `goto-section` / `section-end` behavior;
- `goto-lemma` across `Lemma`, `Theorem`, `Remark`, `Corollary`, and `Fact` declarations;
- `lemma-end` for multi-line and one-line proofs;
- `next-lemma` search-forward behavior and skipping the current lemma.

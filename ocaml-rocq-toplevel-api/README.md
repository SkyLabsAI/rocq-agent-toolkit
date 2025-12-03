Simple Rocq Toplevel API
========================

This OCaml library allows interactively running (and reverting) Rocq commands,
as is typically done in a toplevel (think `rocq top` / `coqtop`). The (simple)
interface of the library is found in `lib/api/rocq_toplevel.mli`.

Implementation / Architecture
-----------------------------

The source code is split into the following four components:
- a shared data interface in `lib/data/` (not part of the API)
- a (private) executable (`rocq-toplevel-api.private`) in `bin/toplevel/`,
- the actual (public) API in `lib/api/`.
- a debug toplevel executable (`rocq-toplevel-api.tester`) in `bin/tester/`.

The current implementation confines interactions with Rocq's internal state to
separate processes (one per toplevel). Thanks to this approach, we do not need
to think too hard about the Rocq state, especially when linking together tools
that all rely on Rocq.

**NOTE:** Using separate processes is not necessary, and other interfaces like
`rocq-lsp` and `vsrocq` directly interact with Rocq. Although this allows them
to be more efficient, our library has simplicity on its side, which helps make
it very reliable.

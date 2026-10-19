Simple (Process-Isolated) Rocq Toplevel API
===========================================

The API is accessed via the `rocq-simple-api.api` ocamlfind package. The main
interface is declared in file `lib/api/rocq_toplevel.mli`. It allows running /
reverting Rocq commands, as is typically done in a toplevel like `rocq top`,
as well as other operations described below.

### Implementation / Architecture

The source code is split into the following four components:
- a shared data interface in `lib/internal/` (not part of the API)
- a (private) executable in `bin/private-toplevel/`,
- the actual (public) API in `lib/api/rocq_toplevel.ml`.
- a debug toplevel executable (`rocq-simple-api.toplevel`) in `bin/toplevel/`.

The current implementation confines interactions with Rocq's internal state to
separate processes (one per toplevel). Thanks to this approach, we do not need
to think too hard about the Rocq state, especially when linking together tools
that all rely on Rocq.

**NOTE:** Using separate processes is not necessary, and other interfaces like
`rocq-lsp` and `vsrocq` directly interact with Rocq. Although this allows them
to be more efficient, our library has simplicity on its side, which helps make
it very reliable.

### Toplevel Forking

The API allow forking the top-level, which can be used to attempt different
interactions at the same time, without risking them interfering.

### Sentence-Splitting

The top-level API also allows splitting Rocq sources into a list of sentences,
either blank characters (including comments) or a command.

A sentence-splitting tool called `rocq-split` is also provided. It can be used
as follows.
```sh
$ rocq-split dir/test.v -- -Q dir test.dir
{
  "items": [
    ...
  ]
}
```

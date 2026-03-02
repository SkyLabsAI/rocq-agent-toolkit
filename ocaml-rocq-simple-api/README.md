Collection of Simple (Process-Isolated) Rocq APIs
=================================================

The APIs are accessed via the `rocq-simple-api.api` ocamlfind package.

Simple Rocq Toplevel API
------------------------

This OCaml library (module `Rocq_toplevel`) allows interactively running (and
reverting) Rocq commands, as is typically done in a toplevel like `rocq top`.
The interface of the library is found in `lib/api/rocq_toplevel.mli`.

### Implementation / Architecture

The source code is split into the following four components:
- a shared data interface in `lib/data/` (not part of the API)
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

Sentence-Splitter
-----------------

This OCaml library (module `Rocq_split`) allows splitting Rocq sources into a
list of sentences, either blank characters (including comments) or a command.
The interface of the library is found in `lib/api/rocq_split.mli`.

Note that a sentence-splitting tool called `rocq-split` is also provided. It
can be used as follows.

```sh
$ rocq-split dir/test.v -- -Q dir test.dir
{
  "file": "test.v",
  "dirpath": "test.dir.test",
  "items": [
    ...
  ]
}
```

### Implementation / Architecture

The source code is split into the following four components:
- a shared data interface in `lib/data/` (not part of the API)
- a (private) executable in `bin/private-splitter/`,
- the actual (public) API in `lib/api/rocq_split.ml`.
- a splitter executable (`rocq-split`) in `bin/splitter/`.

The current implementation confines interactions with Rocq's internal state to
separate processes (one per sentence-splitter call). Thanks to this approach,
we do not need to think too hard about the Rocq state, especially when linking
together tools that all rely on Rocq.

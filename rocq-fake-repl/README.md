Fake Rocq Repl
==============

Utility meant to be used in combination with `dune coq top` to extract the
suitable command-line arguments for a given Rocq source file.

Usage
-----

Within a `dune` project, extracting the command line arguments can be done
as follows.
```sh
dune coq top --toplevel rocq-fake-repl <PATH_TO_ROCQ_FILE>
```
The above command prints the command-line options to its standard output, with
one option per line.

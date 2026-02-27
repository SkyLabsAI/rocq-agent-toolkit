Tool for Splitting Rocq Sources
===============================

This utility (and the underlying OCaml library) can be used to chop Rocq
(previously Coq) theories into individual sentences (vernacular commands
or blanks).

Usage
-----

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

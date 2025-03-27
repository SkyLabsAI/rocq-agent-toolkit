Tool for Splitting Rocq Sources
===============================

This utility (and the underlying OCaml library) can be used to chop Rocq
(previously Coq) theories into individual sentences (vernacular commands
or blanks).

Usage
-----

```sh
$ rocq_split -Q dir test.dir dir/test.v
{
  "file": "test.v",
  "dirpath": "test.dir.test",
  "items": [
    ...
  ]
}
```

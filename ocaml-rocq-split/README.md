Split Rocq Sources
==================

This utility can be used to chop Rocq (previously Coq) source files into the
individual commands (and blanks) they contain.

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

Build an Rocq source file to produce a vo.

  $ touch stale.v
  $ rocq c -Q . test.dir stale.v

Change the version number to 50.0.0 so that it looks stale.

  $ od -Ax -tx1z stale.vo | grep "^000000"
  000000 43 6f 71 21 00 01 60 bb 00 00 00 00 00 00 01 64  >Coq!..`........d<
  $ printf '\x00\x07\xa1\x20' | dd of=stale.vo bs=1 seek=4 conv=notrunc status=none
  $ od -Ax -tx1z stale.vo | grep "^000000"
  000000 43 6f 71 21 00 07 a1 20 00 00 00 00 00 00 01 64  >Coq!... .......d<

Split a test-file that imports the stale vo file.

  $ cat > test.v <<EOF
  > About nat.
  > Require Import test.dir.stale.
  > EOF

  $ rocq-split test.v -- -Q . test.dir
  {
    "error": "Error when parsing .vo (from file $TESTCASE_ROOT/stale.vo) for library test.dir.stale: File $TESTCASE_ROOT/stale.vo\nhas bad version number 500000 (expected 90299). It is corrupted or was\ncompiled with another version of Rocq.",
    "loc": null,
    "Items": [
      {
        "kind": { "controls": [], "tag": "Print", "pure": true },
        "text": "About nat.",
        "bp": 0,
        "ep": 10
      },
      {
        "kind": "blanks",
        "text": "\nRequire Import test.dir.stale.\n",
        "bp": 10,
        "ep": 42
      }
    ]
  }
  [1]

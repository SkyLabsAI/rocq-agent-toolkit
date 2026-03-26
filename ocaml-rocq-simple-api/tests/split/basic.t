  $ cat > test.v <<EOF
  > Require Import Stdlib.ZArith.BinInt.
  > 
  > About nil.
  > Search cons.    Definition junk :=
  > 
  > 
  > nat.
  > Check 12 < 42 <= 100.
  > 
  > 
  > Theorem test : forall x : nat, x = x.
  > Proof.
  >   intro x.
  >   reflexivity.
  > Qed.
  > 
  > Goal True /\ True.
  > Proof.
  >   split.
  >   2:{idtac. }
  >   -idtac. admit.
  >   -idtac. admit.
  > Admitted.
  > 
  > EOF

  $ rocq-split test.v -- -Q . test.dir
  {
    "file": "test.v",
    "dirpath": "test.dir.test",
    "items": [
      {
        "kind": { "controls": [], "tag": "Require", "pure": false },
        "text": "Require Import Stdlib.ZArith.BinInt.",
        "bp": 0,
        "ep": 36
      },
      { "kind": "blanks", "text": "\n\n", "bp": 36, "ep": 38 },
      {
        "kind": { "controls": [], "tag": "Print", "pure": true },
        "text": "About nil.",
        "bp": 38,
        "ep": 48
      },
      { "kind": "blanks", "text": "\n", "bp": 48, "ep": 49 },
      {
        "kind": { "controls": [], "tag": "Search", "pure": true },
        "text": "Search cons.",
        "bp": 49,
        "ep": 61
      },
      { "kind": "blanks", "text": "    ", "bp": 61, "ep": 65 },
      {
        "kind": { "controls": [], "tag": "Definition", "pure": true },
        "text": "Definition junk :=\n\n\nnat.",
        "bp": 65,
        "ep": 90
      },
      { "kind": "blanks", "text": "\n", "bp": 90, "ep": 91 },
      {
        "kind": { "controls": [], "tag": "CheckMayEval", "pure": true },
        "text": "Check 12 < 42 <= 100.",
        "bp": 91,
        "ep": 112
      },
      { "kind": "blanks", "text": "\n\n\n", "bp": 112, "ep": 115 },
      {
        "kind": { "controls": [], "tag": "StartTheoremProof", "pure": true },
        "text": "Theorem test : forall x : nat, x = x.",
        "bp": 115,
        "ep": 152
      },
      { "kind": "blanks", "text": "\n", "bp": 152, "ep": 153 },
      {
        "kind": { "controls": [], "tag": "Proof", "pure": true },
        "text": "Proof.",
        "bp": 153,
        "ep": 159
      },
      { "kind": "blanks", "text": "\n  ", "bp": 159, "ep": 162 },
      {
        "kind": { "controls": [], "tag": "Extend", "pure": false },
        "text": "intro x.",
        "bp": 162,
        "ep": 170
      },
      { "kind": "blanks", "text": "\n  ", "bp": 170, "ep": 173 },
      {
        "kind": { "controls": [], "tag": "Extend", "pure": false },
        "text": "reflexivity.",
        "bp": 173,
        "ep": 185
      },
      { "kind": "blanks", "text": "\n", "bp": 185, "ep": 186 },
      {
        "kind": { "controls": [], "tag": "EndProof", "pure": true },
        "text": "Qed.",
        "bp": 186,
        "ep": 190
      },
      { "kind": "blanks", "text": "\n\n", "bp": 190, "ep": 192 },
      {
        "kind": { "controls": [], "tag": "Definition", "pure": true },
        "text": "Goal True /\\ True.",
        "bp": 192,
        "ep": 210
      },
      { "kind": "blanks", "text": "\n", "bp": 210, "ep": 211 },
      {
        "kind": { "controls": [], "tag": "Proof", "pure": true },
        "text": "Proof.",
        "bp": 211,
        "ep": 217
      },
      { "kind": "blanks", "text": "\n  ", "bp": 217, "ep": 220 },
      {
        "kind": { "controls": [], "tag": "Extend", "pure": false },
        "text": "split.",
        "bp": 220,
        "ep": 226
      },
      { "kind": "blanks", "text": "\n  ", "bp": 226, "ep": 229 },
      {
        "kind": { "controls": [], "tag": "Subproof", "pure": true },
        "text": "2:{",
        "bp": 229,
        "ep": 232
      },
      {
        "kind": { "controls": [], "tag": "Extend", "pure": false },
        "text": "idtac.",
        "bp": 232,
        "ep": 238
      },
      { "kind": "blanks", "text": " ", "bp": 238, "ep": 239 },
      {
        "kind": { "controls": [], "tag": "EndSubproof", "pure": true },
        "text": "}",
        "bp": 239,
        "ep": 240
      },
      { "kind": "blanks", "text": "\n  ", "bp": 240, "ep": 243 },
      {
        "kind": { "controls": [], "tag": "Bullet", "pure": true },
        "text": "-",
        "bp": 243,
        "ep": 244
      },
      {
        "kind": { "controls": [], "tag": "Extend", "pure": false },
        "text": "idtac.",
        "bp": 244,
        "ep": 250
      },
      { "kind": "blanks", "text": " ", "bp": 250, "ep": 251 },
      {
        "kind": { "controls": [], "tag": "Extend", "pure": false },
        "text": "admit.",
        "bp": 251,
        "ep": 257
      },
      { "kind": "blanks", "text": "\n  ", "bp": 257, "ep": 260 },
      {
        "kind": { "controls": [], "tag": "Bullet", "pure": true },
        "text": "-",
        "bp": 260,
        "ep": 261
      },
      {
        "kind": { "controls": [], "tag": "Extend", "pure": false },
        "text": "idtac.",
        "bp": 261,
        "ep": 267
      },
      { "kind": "blanks", "text": " ", "bp": 267, "ep": 268 },
      {
        "kind": { "controls": [], "tag": "Extend", "pure": false },
        "text": "admit.",
        "bp": 268,
        "ep": 274
      },
      { "kind": "blanks", "text": "\n", "bp": 274, "ep": 275 },
      {
        "kind": { "controls": [], "tag": "EndProof", "pure": true },
        "text": "Admitted.",
        "bp": 275,
        "ep": 284
      },
      { "kind": "blanks", "text": "\n\n", "bp": 284, "ep": 286 }
    ]
  }

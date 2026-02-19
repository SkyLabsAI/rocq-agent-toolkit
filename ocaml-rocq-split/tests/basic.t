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
  > EOF

  $ rocq_split -Q . test.dir test.v
  {
    "file": "test.v",
    "dirpath": "test.dir.test",
    "items": [
      {
        "kind": "synterp:Require",
        "text": "Require Import Stdlib.ZArith.BinInt.",
        "bp": 0,
        "ep": 36
      },
      { "kind": "blanks", "text": "\n\n", "bp": 36, "ep": 38 },
      { "kind": "synpure:Print", "text": "About nil.", "bp": 38, "ep": 48 },
      { "kind": "blanks", "text": "\n", "bp": 48, "ep": 49 },
      { "kind": "synpure:Search", "text": "Search cons.", "bp": 49, "ep": 61 },
      { "kind": "blanks", "text": "    ", "bp": 61, "ep": 65 },
      {
        "kind": "synpure:Definition",
        "text": "Definition junk :=\n\n\nnat.",
        "bp": 65,
        "ep": 90
      },
      { "kind": "blanks", "text": "\n", "bp": 90, "ep": 91 },
      {
        "kind": "synpure:CheckMayEval",
        "text": "Check 12 < 42 <= 100.",
        "bp": 91,
        "ep": 112
      },
      { "kind": "blanks", "text": "\n\n\n", "bp": 112, "ep": 115 },
      {
        "kind": "synpure:StartTheoremProof",
        "text": "Theorem test : forall x : nat, x = x.",
        "bp": 115,
        "ep": 152
      },
      { "kind": "blanks", "text": "\n", "bp": 152, "ep": 153 },
      { "kind": "synpure:Proof", "text": "Proof.", "bp": 153, "ep": 159 },
      { "kind": "blanks", "text": "\n  ", "bp": 159, "ep": 162 },
      { "kind": "synterp:Extend", "text": "intro x.", "bp": 162, "ep": 170 },
      { "kind": "blanks", "text": "\n  ", "bp": 170, "ep": 173 },
      {
        "kind": "synterp:Extend",
        "text": "reflexivity.",
        "bp": 173,
        "ep": 185
      },
      { "kind": "blanks", "text": "\n", "bp": 185, "ep": 186 },
      { "kind": "synpure:EndProof", "text": "Qed.", "bp": 186, "ep": 190 },
      { "kind": "blanks", "text": "\n\n", "bp": 190, "ep": 192 }
    ]
  }

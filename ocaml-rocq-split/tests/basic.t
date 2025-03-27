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
  > EOF

  $ rocq_split -Q . test.dir test.v
  {
    "file": "test.v",
    "dirpath": "test.dir.test",
    "items": [
      {
        "cmd": "Require Import Stdlib.ZArith.BinInt.",
        "cat": "synterp",
        "bp": 0,
        "ep": 36
      },
      { "blanks": "\n\n", "bp": 36, "ep": 38 },
      { "cmd": "About nil.", "cat": "synpure", "bp": 38, "ep": 48 },
      { "blanks": "\n", "bp": 48, "ep": 49 },
      { "cmd": "Search cons.", "cat": "synpure", "bp": 49, "ep": 61 },
      { "blanks": "    ", "bp": 61, "ep": 65 },
      {
        "cmd": "Definition junk :=\n\n\nnat.",
        "cat": "synpure",
        "bp": 65,
        "ep": 90
      },
      { "blanks": "\n", "bp": 90, "ep": 91 },
      { "cmd": "Check 12 < 42 <= 100.", "cat": "synpure", "bp": 91, "ep": 112 },
      { "blanks": "\n\n\n", "bp": 112, "ep": 115 },
      {
        "cmd": "Theorem test : forall x : nat, x = x.",
        "cat": "synpure",
        "bp": 115,
        "ep": 152
      },
      { "blanks": "\n", "bp": 152, "ep": 153 },
      { "cmd": "Proof.", "cat": "synpure", "bp": 153, "ep": 159 },
      { "blanks": "\n  ", "bp": 159, "ep": 162 },
      { "cmd": "intro x.", "cat": "synterp", "bp": 162, "ep": 170 },
      { "blanks": "\n  ", "bp": 170, "ep": 173 },
      { "cmd": "reflexivity.", "cat": "synterp", "bp": 173, "ep": 185 },
      { "blanks": "\n", "bp": 185, "ep": 186 },
      { "cmd": "Qed.", "cat": "synpure", "bp": 186, "ep": 190 }
    ]
  }

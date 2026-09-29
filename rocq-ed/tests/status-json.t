  $ cat > test.v <<EOF
  > Theorem test : forall x : nat, x = x.
  > Proof.
  >   intro x.
  >   reflexivity.
  > Qed.
  > EOF

  $ cat > dune-project <<EOF
  > (lang dune 3.21)
  > (using rocq 0.11)
  > EOF

  $ cat > dune <<EOF
  > (rocq.theory
  >  (name text))
  > EOF

The JSON status separates the complete document around the cursor. Outside of
proof mode, there are no current goals.

  $ eval $(rocq-ed init test.v)
  $ rocq-ed status --json
  {
    "prefix": [],
    "suffix": [
      {
        "kind": "command",
        "text": "Theorem test : forall x : nat, x = x.",
        "data": {
          "kind": "StartTheoremProof",
          "pure": true,
          "attrs": { "ids": [ "test" ], "kind": "Theorem" }
        }
      },
      { "kind": "blanks", "text": "\n" },
      {
        "kind": "command",
        "text": "Proof.",
        "data": { "kind": "Proof", "pure": true }
      },
      { "kind": "blanks", "text": "\n  " },
      { "kind": "command", "text": "intro x.", "data": { "kind": "Extend" } },
      { "kind": "blanks", "text": "\n  " },
      {
        "kind": "command",
        "text": "reflexivity.",
        "data": { "kind": "Extend" }
      },
      { "kind": "blanks", "text": "\n" },
      {
        "kind": "command",
        "text": "Qed.",
        "data": {
          "kind": "EndProof",
          "pure": true,
          "attrs": { "kind": "Qed" }
        }
      },
      { "kind": "blanks", "text": "\n" }
    ],
    "goals": null
  }

Within a proof, goals are decomposed into hypotheses and conclusions.

  $ rocq-ed steps --count-items 5
  $ rocq-ed status --json
  {
    "prefix": [
      {
        "kind": "command",
        "offset": 0,
        "text": "Theorem test : forall x : nat, x = x.",
        "data": {
          "kind": "StartTheoremProof",
          "pure": true,
          "attrs": { "ids": [ "test" ], "kind": "Theorem" }
        }
      },
      { "kind": "blanks", "offset": 37, "text": "\n" },
      {
        "kind": "command",
        "offset": 38,
        "text": "Proof.",
        "data": { "kind": "Proof", "pure": true }
      },
      { "kind": "blanks", "offset": 44, "text": "\n  " },
      {
        "kind": "command",
        "offset": 47,
        "text": "intro x.",
        "data": { "kind": "Extend" }
      }
    ],
    "suffix": [
      { "kind": "blanks", "text": "\n  " },
      {
        "kind": "command",
        "text": "reflexivity.",
        "data": { "kind": "Extend" }
      },
      { "kind": "blanks", "text": "\n" },
      {
        "kind": "command",
        "text": "Qed.",
        "data": {
          "kind": "EndProof",
          "pure": true,
          "attrs": { "kind": "Qed" }
        }
      },
      { "kind": "blanks", "text": "\n" }
    ],
    "goals": [
      { "hyps": [ { "name": "x", "type": "nat" } ], "goal": "x = x" }
    ]
  }
  $ rocq-ed stop
